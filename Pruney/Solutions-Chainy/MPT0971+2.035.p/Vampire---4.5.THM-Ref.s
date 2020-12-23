%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 172 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 ( 628 expanded)
%              Number of equality atoms :   45 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f94,f103,f109,f181,f198,f220,f244,f296])).

% (9759)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (9774)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (9756)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (9770)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (9775)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (9754)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (9757)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f296,plain,
    ( ~ spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_13
    | spl11_14 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_13
    | spl11_14 ),
    inference(subsumption_resolution,[],[f277,f245])).

fof(f245,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(sK7,sK8),X0),sK8)
    | ~ spl11_2
    | spl11_14 ),
    inference(unit_resulting_resolution,[],[f243,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
        | r2_hidden(X0,sK5) )
    | ~ spl11_2 ),
    inference(resolution,[],[f69,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6))
        | ~ r2_hidden(X0,sK8) )
    | ~ spl11_2 ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl11_2
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

% (9775)Refutation not found, incomplete strategy% (9775)------------------------------
% (9775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9775)Termination reason: Refutation not found, incomplete strategy

% (9775)Memory used [KB]: 10618
% (9775)Time elapsed: 0.094 s
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

% (9775)------------------------------
% (9775)------------------------------
fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f243,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),sK5)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl11_14
  <=> r2_hidden(sK10(sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f277,plain,
    ( r2_hidden(k4_tarski(sK10(sK7,sK8),sK7),sK8)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f116,f219,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | ~ sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f219,plain,
    ( sP3(sK7,sK10(sK7,sK8),sK8)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl11_13
  <=> sP3(sK7,sK10(sK7,sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f116,plain,
    ( ! [X0,X1] : sP4(sK8,X0,X1)
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f100,f93,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP4(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f18,f24,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f93,plain,
    ( v1_funct_1(sK8)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl11_4
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f100,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl11_5
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f244,plain,
    ( ~ spl11_14
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f239,f217,f241])).

fof(f239,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),sK5)
    | ~ spl11_13 ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),sK5)
    | sK7 != sK7
    | ~ spl11_13 ),
    inference(resolution,[],[f219,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0,sK8)
      | ~ r2_hidden(X0,sK5)
      | sK7 != X1 ) ),
    inference(superposition,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X4] :
      ( sK7 != k1_funct_1(sK8,X4)
      | ~ r2_hidden(X4,sK5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK7 != k1_funct_1(sK8,X4)
        | ~ r2_hidden(X4,sK5) )
    & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f11,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK7 != k1_funct_1(sK8,X4)
          | ~ r2_hidden(X4,sK5) )
      & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f220,plain,
    ( spl11_13
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f201,f190,f217])).

fof(f190,plain,
    ( spl11_10
  <=> sP0(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f201,plain,
    ( sP3(sK7,sK10(sK7,sK8),sK8)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f154])).

fof(f154,plain,(
    ! [X4,X3] :
      ( sP3(X4,sK10(X4,X3),X3)
      | ~ sP0(X4,X3) ) ),
    inference(subsumption_resolution,[],[f153,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK10(X0,X1)) = X0
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK10(X0,X1)) = X0
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f153,plain,(
    ! [X4,X3] :
      ( sP3(X4,sK10(X4,X3),X3)
      | ~ r2_hidden(sK10(X4,X3),k1_relat_1(X3))
      | ~ sP0(X4,X3) ) ),
    inference(superposition,[],[f74,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK10(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X1] :
      ( sP3(k1_funct_1(X2,X1),X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f192,plain,
    ( sP0(sK7,sK8)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f198,plain,
    ( spl11_10
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f197,f178,f106,f190])).

fof(f106,plain,
    ( spl11_6
  <=> sP2(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f178,plain,
    ( spl11_9
  <=> r2_hidden(sK7,k2_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f197,plain,
    ( sP0(sK7,sK8)
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f187,f108])).

fof(f108,plain,
    ( sP2(sK8)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f187,plain,
    ( sP0(sK7,sK8)
    | ~ sP2(sK8)
    | ~ spl11_9 ),
    inference(resolution,[],[f180,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sP0(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sP0(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f180,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl11_9
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f176,f81,f76,f178])).

fof(f76,plain,
    ( spl11_1
  <=> r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f176,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f170,f83])).

fof(f170,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl11_1 ),
    inference(superposition,[],[f78,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f78,plain,
    ( r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f109,plain,
    ( spl11_6
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f104,f98,f91,f106])).

fof(f104,plain,
    ( sP2(sK8)
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f93,f100,f59])).

fof(f59,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f21,f20,f19])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f103,plain,
    ( spl11_5
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f102,f81,f98])).

fof(f102,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f96,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f96,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | ~ spl11_2 ),
    inference(resolution,[],[f49,f83])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f94,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (9771)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (9768)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (9767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (9764)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (9758)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (9760)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (9761)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (9771)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (9773)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (9769)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f79,f84,f94,f103,f109,f181,f198,f220,f244,f296])).
% 1.33/0.53  % (9759)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.33/0.53  % (9774)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.33/0.53  % (9756)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.33/0.53  % (9770)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.33/0.54  % (9775)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.33/0.54  % (9754)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (9757)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  fof(f296,plain,(
% 1.33/0.54    ~spl11_2 | ~spl11_4 | ~spl11_5 | ~spl11_13 | spl11_14),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f295])).
% 1.33/0.54  fof(f295,plain,(
% 1.33/0.54    $false | (~spl11_2 | ~spl11_4 | ~spl11_5 | ~spl11_13 | spl11_14)),
% 1.33/0.54    inference(subsumption_resolution,[],[f277,f245])).
% 1.33/0.54  fof(f245,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK10(sK7,sK8),X0),sK8)) ) | (~spl11_2 | spl11_14)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f243,f147])).
% 1.33/0.54  fof(f147,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK8) | r2_hidden(X0,sK5)) ) | ~spl11_2),
% 1.33/0.54    inference(resolution,[],[f69,f146])).
% 1.33/0.54  fof(f146,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) | ~r2_hidden(X0,sK8)) ) | ~spl11_2),
% 1.33/0.54    inference(resolution,[],[f61,f83])).
% 1.33/0.54  fof(f83,plain,(
% 1.33/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl11_2),
% 1.33/0.54    inference(avatar_component_clause,[],[f81])).
% 1.33/0.54  fof(f81,plain,(
% 1.33/0.54    spl11_2 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f2])).
% 1.33/0.54  % (9775)Refutation not found, incomplete strategy% (9775)------------------------------
% 1.33/0.54  % (9775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (9775)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (9775)Memory used [KB]: 10618
% 1.33/0.54  % (9775)Time elapsed: 0.094 s
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.33/0.54  % (9775)------------------------------
% 1.33/0.54  % (9775)------------------------------
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.33/0.54    inference(flattening,[],[f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.33/0.54    inference(nnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.33/0.54  fof(f243,plain,(
% 1.33/0.54    ~r2_hidden(sK10(sK7,sK8),sK5) | spl11_14),
% 1.33/0.54    inference(avatar_component_clause,[],[f241])).
% 1.33/0.54  fof(f241,plain,(
% 1.33/0.54    spl11_14 <=> r2_hidden(sK10(sK7,sK8),sK5)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.33/0.54  fof(f277,plain,(
% 1.33/0.54    r2_hidden(k4_tarski(sK10(sK7,sK8),sK7),sK8) | (~spl11_4 | ~spl11_5 | ~spl11_13)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f116,f219,f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | ~sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f38])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP4(X0,X1,X2))),
% 1.33/0.54    inference(rectify,[],[f37])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP4(X2,X0,X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.33/0.54  fof(f219,plain,(
% 1.33/0.54    sP3(sK7,sK10(sK7,sK8),sK8) | ~spl11_13),
% 1.33/0.54    inference(avatar_component_clause,[],[f217])).
% 1.33/0.54  fof(f217,plain,(
% 1.33/0.54    spl11_13 <=> sP3(sK7,sK10(sK7,sK8),sK8)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.33/0.54  fof(f116,plain,(
% 1.33/0.54    ( ! [X0,X1] : (sP4(sK8,X0,X1)) ) | (~spl11_4 | ~spl11_5)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f100,f93,f68])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.54    inference(definition_folding,[],[f18,f24,f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.54    inference(flattening,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.33/0.54  fof(f93,plain,(
% 1.33/0.54    v1_funct_1(sK8) | ~spl11_4),
% 1.33/0.54    inference(avatar_component_clause,[],[f91])).
% 1.33/0.54  fof(f91,plain,(
% 1.33/0.54    spl11_4 <=> v1_funct_1(sK8)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.33/0.54  fof(f100,plain,(
% 1.33/0.54    v1_relat_1(sK8) | ~spl11_5),
% 1.33/0.54    inference(avatar_component_clause,[],[f98])).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    spl11_5 <=> v1_relat_1(sK8)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.33/0.54  fof(f244,plain,(
% 1.33/0.54    ~spl11_14 | ~spl11_13),
% 1.33/0.54    inference(avatar_split_clause,[],[f239,f217,f241])).
% 1.33/0.54  fof(f239,plain,(
% 1.33/0.54    ~r2_hidden(sK10(sK7,sK8),sK5) | ~spl11_13),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f235])).
% 1.33/0.54  fof(f235,plain,(
% 1.33/0.54    ~r2_hidden(sK10(sK7,sK8),sK5) | sK7 != sK7 | ~spl11_13),
% 1.33/0.54    inference(resolution,[],[f219,f131])).
% 1.33/0.54  fof(f131,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~sP3(X1,X0,sK8) | ~r2_hidden(X0,sK5) | sK7 != X1) )),
% 1.33/0.54    inference(superposition,[],[f48,f66])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | ~sP3(X0,X1,X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f41])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP3(X0,X1,X2)))),
% 1.33/0.54    inference(rectify,[],[f40])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.33/0.54    inference(flattening,[],[f39])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.33/0.54    inference(nnf_transformation,[],[f23])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    ( ! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f11,f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.33/0.54    inference(flattening,[],[f10])).
% 1.33/0.54  fof(f10,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,negated_conjecture,(
% 1.33/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 1.33/0.54    inference(negated_conjecture,[],[f8])).
% 1.33/0.54  fof(f8,conjecture,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).
% 1.33/0.54  fof(f220,plain,(
% 1.33/0.54    spl11_13 | ~spl11_10),
% 1.33/0.54    inference(avatar_split_clause,[],[f201,f190,f217])).
% 1.33/0.54  fof(f190,plain,(
% 1.33/0.54    spl11_10 <=> sP0(sK7,sK8)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.33/0.54  fof(f201,plain,(
% 1.33/0.54    sP3(sK7,sK10(sK7,sK8),sK8) | ~spl11_10),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f192,f154])).
% 1.33/0.54  fof(f154,plain,(
% 1.33/0.54    ( ! [X4,X3] : (sP3(X4,sK10(X4,X3),X3) | ~sP0(X4,X3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f153,f56])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.33/0.54    inference(rectify,[],[f33])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 1.33/0.54    inference(nnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.33/0.54  fof(f153,plain,(
% 1.33/0.54    ( ! [X4,X3] : (sP3(X4,sK10(X4,X3),X3) | ~r2_hidden(sK10(X4,X3),k1_relat_1(X3)) | ~sP0(X4,X3)) )),
% 1.33/0.54    inference(superposition,[],[f74,f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_funct_1(X1,sK10(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    ( ! [X2,X1] : (sP3(k1_funct_1(X2,X1),X1,X2) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 1.33/0.54    inference(equality_resolution,[],[f67])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f41])).
% 1.33/0.54  fof(f192,plain,(
% 1.33/0.54    sP0(sK7,sK8) | ~spl11_10),
% 1.33/0.54    inference(avatar_component_clause,[],[f190])).
% 1.33/0.54  fof(f198,plain,(
% 1.33/0.54    spl11_10 | ~spl11_6 | ~spl11_9),
% 1.33/0.54    inference(avatar_split_clause,[],[f197,f178,f106,f190])).
% 1.33/0.54  fof(f106,plain,(
% 1.33/0.54    spl11_6 <=> sP2(sK8)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.33/0.54  fof(f178,plain,(
% 1.33/0.54    spl11_9 <=> r2_hidden(sK7,k2_relat_1(sK8))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.33/0.54  fof(f197,plain,(
% 1.33/0.54    sP0(sK7,sK8) | (~spl11_6 | ~spl11_9)),
% 1.33/0.54    inference(subsumption_resolution,[],[f187,f108])).
% 1.33/0.54  fof(f108,plain,(
% 1.33/0.54    sP2(sK8) | ~spl11_6),
% 1.33/0.54    inference(avatar_component_clause,[],[f106])).
% 1.33/0.54  fof(f187,plain,(
% 1.33/0.54    sP0(sK7,sK8) | ~sP2(sK8) | ~spl11_9),
% 1.33/0.54    inference(resolution,[],[f180,f123])).
% 1.33/0.54  fof(f123,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP0(X0,X1) | ~sP2(X1)) )),
% 1.33/0.54    inference(resolution,[],[f52,f72])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 1.33/0.54    inference(equality_resolution,[],[f50])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP0(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP0(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.33/0.54    inference(rectify,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.33/0.54    inference(nnf_transformation,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 1.33/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.33/0.54  fof(f180,plain,(
% 1.33/0.54    r2_hidden(sK7,k2_relat_1(sK8)) | ~spl11_9),
% 1.33/0.54    inference(avatar_component_clause,[],[f178])).
% 1.33/0.54  fof(f181,plain,(
% 1.33/0.54    spl11_9 | ~spl11_1 | ~spl11_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f176,f81,f76,f178])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    spl11_1 <=> r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.33/0.54  fof(f176,plain,(
% 1.33/0.54    r2_hidden(sK7,k2_relat_1(sK8)) | (~spl11_1 | ~spl11_2)),
% 1.33/0.54    inference(subsumption_resolution,[],[f170,f83])).
% 1.33/0.54  fof(f170,plain,(
% 1.33/0.54    r2_hidden(sK7,k2_relat_1(sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl11_1),
% 1.33/0.54    inference(superposition,[],[f78,f62])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) | ~spl11_1),
% 1.33/0.54    inference(avatar_component_clause,[],[f76])).
% 1.33/0.54  fof(f109,plain,(
% 1.33/0.54    spl11_6 | ~spl11_4 | ~spl11_5),
% 1.33/0.54    inference(avatar_split_clause,[],[f104,f98,f91,f106])).
% 1.33/0.54  fof(f104,plain,(
% 1.33/0.54    sP2(sK8) | (~spl11_4 | ~spl11_5)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f93,f100,f59])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.54    inference(definition_folding,[],[f14,f21,f20,f19])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.54    inference(flattening,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.33/0.54  fof(f103,plain,(
% 1.33/0.54    spl11_5 | ~spl11_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f102,f81,f98])).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    v1_relat_1(sK8) | ~spl11_2),
% 1.33/0.54    inference(subsumption_resolution,[],[f96,f60])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.33/0.54  fof(f96,plain,(
% 1.33/0.54    v1_relat_1(sK8) | ~v1_relat_1(k2_zfmisc_1(sK5,sK6)) | ~spl11_2),
% 1.33/0.54    inference(resolution,[],[f49,f83])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    spl11_4),
% 1.33/0.54    inference(avatar_split_clause,[],[f44,f91])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    v1_funct_1(sK8)),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f84,plain,(
% 1.33/0.54    spl11_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f46,f81])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f79,plain,(
% 1.33/0.54    spl11_1),
% 1.33/0.54    inference(avatar_split_clause,[],[f47,f76])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (9771)------------------------------
% 1.33/0.54  % (9771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (9771)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (9771)Memory used [KB]: 10746
% 1.33/0.54  % (9771)Time elapsed: 0.120 s
% 1.33/0.54  % (9771)------------------------------
% 1.33/0.54  % (9771)------------------------------
% 1.33/0.54  % (9753)Success in time 0.183 s
%------------------------------------------------------------------------------
