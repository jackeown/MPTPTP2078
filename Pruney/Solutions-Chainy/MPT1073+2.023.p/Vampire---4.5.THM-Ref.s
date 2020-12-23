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
% DateTime   : Thu Dec  3 13:07:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 349 expanded)
%              Number of leaves         :   17 (  91 expanded)
%              Depth                    :   17
%              Number of atoms          :  354 (1591 expanded)
%              Number of equality atoms :   90 ( 337 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f250,f287,f418,f480])).

fof(f480,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f478,f436])).

fof(f436,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(superposition,[],[f251,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f251,plain,
    ( sK1 != k1_relset_1(sK1,k1_xboole_0,sK3)
    | spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f136,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f136,plain,
    ( sK1 != k1_relset_1(sK1,sK2,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_3
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f478,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f468,f450])).

fof(f450,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f419,f141])).

fof(f419,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl7_8 ),
    inference(superposition,[],[f57,f286])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

% (25831)Refutation not found, incomplete strategy% (25831)------------------------------
% (25831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25831)Termination reason: Refutation not found, incomplete strategy

% (25831)Memory used [KB]: 10618
% (25831)Time elapsed: 0.114 s
% (25831)------------------------------
% (25831)------------------------------
fof(f42,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f468,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f451,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f420,f141])).

fof(f420,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl7_8 ),
    inference(superposition,[],[f58,f286])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f418,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f414,f61])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f414,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_7 ),
    inference(resolution,[],[f352,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f352,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(k1_xboole_0),k1_xboole_0),sK0),k1_xboole_0)
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f350,f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f350,plain,(
    r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(sK3),sK3),sK0),sK3) ),
    inference(resolution,[],[f186,f150])).

fof(f150,plain,(
    r2_hidden(sK0,k2_relat_1(sK3)) ),
    inference(superposition,[],[f59,f114])).

fof(f114,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f81,f58])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK4(X0,k1_relat_1(sK3),sK3),X0),sK3) ) ),
    inference(subsumption_resolution,[],[f183,f106])).

fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK4(X0,k1_relat_1(sK3),sK3),X0),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f76,f108])).

fof(f108,plain,(
    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(resolution,[],[f62,f106])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (25840)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (25857)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (25853)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (25845)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (25855)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f287,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f278,f139,f284,f280])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f270,f252])).

% (25849)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f252,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl7_4 ),
    inference(superposition,[],[f57,f141])).

fof(f270,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f253,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f253,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(superposition,[],[f58,f141])).

fof(f250,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f248,f244])).

fof(f244,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f243,f106])).

fof(f243,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f235,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f235,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f205,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f187,f150])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK4(X0,sK1,sK3),X0),sK3) )
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f186,f146])).

fof(f146,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(superposition,[],[f113,f137])).

fof(f137,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f113,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f248,plain,
    ( sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f221,f60])).

fof(f60,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f221,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f204,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f204,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f189,f150])).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK3))
        | r2_hidden(sK4(X1,sK1,sK3),sK1) )
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f188,f146])).

fof(f188,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(sK4(X1,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f184,f106])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(sK4(X1,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f75,f108])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f142,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f132,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f82,f58])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (25837)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (25843)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (25851)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (25848)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (25832)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (25842)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (25833)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (25841)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (25847)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (25842)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (25836)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (25835)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (25839)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (25854)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (25846)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (25850)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (25844)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (25831)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (25852)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (25834)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f481,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f142,f250,f287,f418,f480])).
% 0.20/0.52  fof(f480,plain,(
% 0.20/0.52    spl7_3 | ~spl7_4 | ~spl7_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f479])).
% 0.20/0.52  fof(f479,plain,(
% 0.20/0.52    $false | (spl7_3 | ~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f478,f436])).
% 0.20/0.52  fof(f436,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (spl7_3 | ~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(superposition,[],[f251,f286])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl7_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f284])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    spl7_8 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    sK1 != k1_relset_1(sK1,k1_xboole_0,sK3) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f136,f141])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    spl7_4 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    sK1 != k1_relset_1(sK1,sK2,sK3) | spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl7_3 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f478,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f468,f450])).
% 0.20/0.52  fof(f450,plain,(
% 0.20/0.52    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(forward_demodulation,[],[f419,f141])).
% 0.20/0.52  fof(f419,plain,(
% 0.20/0.52    v1_funct_2(sK3,k1_xboole_0,sK2) | ~spl7_8),
% 0.20/0.52    inference(superposition,[],[f57,f286])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  % (25831)Refutation not found, incomplete strategy% (25831)------------------------------
% 0.20/0.52  % (25831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25831)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25831)Memory used [KB]: 10618
% 0.20/0.52  % (25831)Time elapsed: 0.114 s
% 0.20/0.52  % (25831)------------------------------
% 0.20/0.52  % (25831)------------------------------
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.20/0.52    inference(negated_conjecture,[],[f18])).
% 0.20/0.52  fof(f18,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.20/0.52  fof(f468,plain,(
% 0.20/0.52    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(resolution,[],[f451,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f451,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_8)),
% 0.20/0.52    inference(forward_demodulation,[],[f420,f141])).
% 0.20/0.52  fof(f420,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl7_8),
% 0.20/0.52    inference(superposition,[],[f58,f286])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f418,plain,(
% 0.20/0.52    ~spl7_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f417])).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    $false | ~spl7_7),
% 0.20/0.52    inference(subsumption_resolution,[],[f414,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl7_7),
% 0.20/0.52    inference(resolution,[],[f352,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(k1_xboole_0),k1_xboole_0),sK0),k1_xboole_0) | ~spl7_7),
% 0.20/0.52    inference(forward_demodulation,[],[f350,f282])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    k1_xboole_0 = sK3 | ~spl7_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f280])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    spl7_7 <=> k1_xboole_0 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(sK3),sK3),sK0),sK3)),
% 0.20/0.52    inference(resolution,[],[f186,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_relat_1(sK3))),
% 0.20/0.52    inference(superposition,[],[f59,f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f81,f58])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK4(X0,k1_relat_1(sK3),sK3),X0),sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f183,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    v1_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f79,f58])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK4(X0,k1_relat_1(sK3),sK3),X0),sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.52    inference(superposition,[],[f76,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f62,f106])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  % (25840)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (25857)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (25853)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (25845)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (25855)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f50,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 1.45/0.54  fof(f49,plain,(
% 1.45/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(rectify,[],[f47])).
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(nnf_transformation,[],[f31])).
% 1.45/0.54  fof(f31,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(ennf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.45/0.54  fof(f287,plain,(
% 1.45/0.54    spl7_7 | spl7_8 | ~spl7_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f278,f139,f284,f280])).
% 1.45/0.54  fof(f278,plain,(
% 1.45/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~spl7_4),
% 1.45/0.54    inference(subsumption_resolution,[],[f270,f252])).
% 1.45/0.54  % (25849)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.54  fof(f252,plain,(
% 1.45/0.54    v1_funct_2(sK3,sK1,k1_xboole_0) | ~spl7_4),
% 1.45/0.54    inference(superposition,[],[f57,f141])).
% 1.45/0.54  fof(f270,plain,(
% 1.45/0.54    ~v1_funct_2(sK3,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~spl7_4),
% 1.45/0.54    inference(resolution,[],[f253,f98])).
% 1.45/0.54  fof(f98,plain,(
% 1.45/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.45/0.54    inference(equality_resolution,[],[f86])).
% 1.45/0.54  fof(f86,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f51])).
% 1.45/0.54  fof(f253,plain,(
% 1.45/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl7_4),
% 1.45/0.54    inference(superposition,[],[f58,f141])).
% 1.45/0.54  fof(f250,plain,(
% 1.45/0.54    ~spl7_3),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f249])).
% 1.45/0.54  fof(f249,plain,(
% 1.45/0.54    $false | ~spl7_3),
% 1.45/0.54    inference(subsumption_resolution,[],[f248,f244])).
% 1.45/0.54  fof(f244,plain,(
% 1.45/0.54    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~spl7_3),
% 1.45/0.54    inference(subsumption_resolution,[],[f243,f106])).
% 1.45/0.54  fof(f243,plain,(
% 1.45/0.54    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~v1_relat_1(sK3) | ~spl7_3),
% 1.45/0.54    inference(subsumption_resolution,[],[f235,f56])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    v1_funct_1(sK3)),
% 1.45/0.54    inference(cnf_transformation,[],[f42])).
% 1.45/0.54  fof(f235,plain,(
% 1.45/0.54    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_3),
% 1.45/0.54    inference(resolution,[],[f205,f89])).
% 1.45/0.54  fof(f89,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f53])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f52])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(nnf_transformation,[],[f38])).
% 1.45/0.54  fof(f38,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f37])).
% 1.45/0.54  fof(f37,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.45/0.54  fof(f205,plain,(
% 1.45/0.54    r2_hidden(k4_tarski(sK4(sK0,sK1,sK3),sK0),sK3) | ~spl7_3),
% 1.45/0.54    inference(resolution,[],[f187,f150])).
% 1.45/0.54  fof(f187,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK4(X0,sK1,sK3),X0),sK3)) ) | ~spl7_3),
% 1.45/0.54    inference(forward_demodulation,[],[f186,f146])).
% 1.45/0.54  fof(f146,plain,(
% 1.45/0.54    sK1 = k1_relat_1(sK3) | ~spl7_3),
% 1.45/0.54    inference(superposition,[],[f113,f137])).
% 1.45/0.54  fof(f137,plain,(
% 1.45/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_3),
% 1.45/0.54    inference(avatar_component_clause,[],[f135])).
% 1.45/0.54  fof(f113,plain,(
% 1.45/0.54    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.45/0.54    inference(resolution,[],[f80,f58])).
% 1.45/0.54  fof(f80,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f14])).
% 1.45/0.54  fof(f14,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.45/0.54  fof(f248,plain,(
% 1.45/0.54    sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~spl7_3),
% 1.45/0.54    inference(resolution,[],[f221,f60])).
% 1.45/0.54  fof(f60,plain,(
% 1.45/0.54    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f42])).
% 1.45/0.54  fof(f221,plain,(
% 1.45/0.54    m1_subset_1(sK4(sK0,sK1,sK3),sK1) | ~spl7_3),
% 1.45/0.54    inference(resolution,[],[f204,f67])).
% 1.45/0.54  fof(f67,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.45/0.54  fof(f204,plain,(
% 1.45/0.54    r2_hidden(sK4(sK0,sK1,sK3),sK1) | ~spl7_3),
% 1.45/0.54    inference(resolution,[],[f189,f150])).
% 1.45/0.54  fof(f189,plain,(
% 1.45/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(sK4(X1,sK1,sK3),sK1)) ) | ~spl7_3),
% 1.45/0.54    inference(forward_demodulation,[],[f188,f146])).
% 1.45/0.54  fof(f188,plain,(
% 1.45/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(sK4(X1,k1_relat_1(sK3),sK3),k1_relat_1(sK3))) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f184,f106])).
% 1.45/0.54  fof(f184,plain,(
% 1.45/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(sK4(X1,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.45/0.54    inference(superposition,[],[f75,f108])).
% 1.45/0.54  fof(f75,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f142,plain,(
% 1.45/0.54    spl7_3 | spl7_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f133,f139,f135])).
% 1.45/0.54  fof(f133,plain,(
% 1.45/0.54    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.45/0.54    inference(subsumption_resolution,[],[f132,f57])).
% 1.45/0.54  fof(f132,plain,(
% 1.45/0.54    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.45/0.54    inference(resolution,[],[f82,f58])).
% 1.45/0.54  fof(f82,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.45/0.54    inference(cnf_transformation,[],[f51])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (25842)------------------------------
% 1.45/0.54  % (25842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (25842)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (25842)Memory used [KB]: 10874
% 1.45/0.54  % (25842)Time elapsed: 0.099 s
% 1.45/0.54  % (25842)------------------------------
% 1.45/0.54  % (25842)------------------------------
% 1.45/0.54  % (25828)Success in time 0.185 s
%------------------------------------------------------------------------------
