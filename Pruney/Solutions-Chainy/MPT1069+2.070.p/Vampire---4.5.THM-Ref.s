%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 315 expanded)
%              Number of leaves         :   47 ( 155 expanded)
%              Depth                    :    9
%              Number of atoms          :  559 (1685 expanded)
%              Number of equality atoms :   81 ( 339 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f115,f127,f137,f143,f147,f159,f167,f175,f180,f192,f198,f201,f204,f223,f230,f231,f233])).

fof(f233,plain,
    ( spl8_2
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f232,f228,f72])).

fof(f72,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f228,plain,
    ( spl8_31
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_31 ),
    inference(resolution,[],[f229,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f229,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f228])).

fof(f231,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK7
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f230,plain,
    ( ~ spl8_4
    | spl8_31
    | spl8_30 ),
    inference(avatar_split_clause,[],[f225,f220,f228,f80])).

fof(f80,plain,
    ( spl8_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f220,plain,
    ( spl8_30
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f225,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl8_30 ),
    inference(resolution,[],[f221,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f221,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( ~ spl8_30
    | ~ spl8_17
    | ~ spl8_20
    | spl8_26 ),
    inference(avatar_split_clause,[],[f216,f190,f157,f141,f220])).

fof(f141,plain,
    ( spl8_17
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f157,plain,
    ( spl8_20
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f190,plain,
    ( spl8_26
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f216,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ r2_hidden(sK5,sK1)
    | ~ spl8_20
    | spl8_26 ),
    inference(resolution,[],[f207,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK5),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK4)) )
    | spl8_26 ),
    inference(resolution,[],[f191,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

% (22728)Refutation not found, incomplete strategy% (22728)------------------------------
% (22728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22728)Termination reason: Refutation not found, incomplete strategy

% (22728)Memory used [KB]: 10746
% (22728)Time elapsed: 0.107 s
% (22728)------------------------------
% (22728)------------------------------
% (22732)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (22707)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f191,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f190])).

fof(f204,plain,
    ( ~ spl8_5
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl8_5
    | spl8_25 ),
    inference(subsumption_resolution,[],[f85,f202])).

fof(f202,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl8_25 ),
    inference(resolution,[],[f188,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f188,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl8_25
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f85,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f201,plain,(
    spl8_27 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl8_27 ),
    inference(resolution,[],[f197,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f197,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl8_27 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_27
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f198,plain,
    ( ~ spl8_27
    | ~ spl8_5
    | spl8_24 ),
    inference(avatar_split_clause,[],[f194,f184,f84,f196])).

fof(f184,plain,
    ( spl8_24
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f194,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl8_5
    | spl8_24 ),
    inference(resolution,[],[f193,f85])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_24 ),
    inference(resolution,[],[f185,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f185,plain,
    ( ~ v1_relat_1(sK4)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f192,plain,
    ( ~ spl8_24
    | ~ spl8_25
    | ~ spl8_6
    | ~ spl8_26
    | spl8_23 ),
    inference(avatar_split_clause,[],[f182,f178,f190,f88,f187,f184])).

fof(f88,plain,
    ( spl8_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f178,plain,
    ( spl8_23
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f182,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl8_23 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl8_23 ),
    inference(superposition,[],[f179,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f179,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl8_23
    | spl8_1
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f176,f172,f68,f178])).

fof(f68,plain,
    ( spl8_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f172,plain,
    ( spl8_22
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f176,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl8_1
    | ~ spl8_22 ),
    inference(superposition,[],[f69,f173])).

fof(f173,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f69,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f175,plain,
    ( ~ spl8_18
    | spl8_22
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f169,f165,f84,f80,f88,f172,f145])).

fof(f145,plain,
    ( spl8_18
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f165,plain,
    ( spl8_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ m1_subset_1(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f169,plain,
    ( ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_21 ),
    inference(resolution,[],[f168,f85])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) )
    | ~ spl8_4
    | ~ spl8_21 ),
    inference(resolution,[],[f166,f81])).

fof(f81,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl8_10
    | ~ spl8_9
    | ~ spl8_7
    | spl8_2
    | spl8_21
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f161,f135,f96,f165,f72,f92,f100,f104])).

fof(f104,plain,
    ( spl8_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f100,plain,
    ( spl8_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f92,plain,
    ( spl8_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f96,plain,
    ( spl8_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f135,plain,
    ( spl8_16
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f160,f136])).

fof(f136,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl8_8 ),
    inference(resolution,[],[f61,f97])).

fof(f97,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

% (22706)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f159,plain,
    ( ~ spl8_9
    | ~ spl8_7
    | spl8_19
    | spl8_20
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f150,f135,f96,f157,f154,f92,f100])).

fof(f154,plain,
    ( spl8_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
        | k1_xboole_0 = sK2
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK3) )
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f149,f136])).

fof(f149,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
        | ~ v1_funct_1(sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f65,f97])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f147,plain,
    ( spl8_18
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f139,f135,f76,f145])).

fof(f76,plain,
    ( spl8_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f139,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(superposition,[],[f77,f136])).

fof(f77,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f143,plain,
    ( spl8_17
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f138,f135,f125,f141])).

fof(f125,plain,
    ( spl8_14
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f138,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(superposition,[],[f126,f136])).

fof(f126,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f137,plain,
    ( spl8_16
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f129,f92,f135])).

fof(f129,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl8_7 ),
    inference(resolution,[],[f63,f93])).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f127,plain,
    ( ~ spl8_5
    | spl8_14
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f122,f76,f125,f84])).

fof(f122,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl8_3 ),
    inference(superposition,[],[f77,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( spl8_12
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f111,f108,f113])).

fof(f113,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f108,plain,
    ( spl8_11
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f111,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_11 ),
    inference(resolution,[],[f54,f109])).

fof(f109,plain,
    ( v1_xboole_0(sK7)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f66,f108])).

fof(f66,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3,f41])).

fof(f41,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f106,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f43,f104])).

fof(f43,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f102,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f49,f80])).

fof(f49,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f50,f76])).

fof(f50,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f51,f72])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f52,f68])).

fof(f52,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (22710)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (22730)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.50  % (22723)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (22736)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (22705)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (22729)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (22709)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (22728)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (22730)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f234,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f115,f127,f137,f143,f147,f159,f167,f175,f180,f192,f198,f201,f204,f223,f230,f231,f233])).
% 0.19/0.52  fof(f233,plain,(
% 0.19/0.52    spl8_2 | ~spl8_31),
% 0.19/0.52    inference(avatar_split_clause,[],[f232,f228,f72])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    spl8_2 <=> k1_xboole_0 = sK1),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.19/0.52  fof(f228,plain,(
% 0.19/0.52    spl8_31 <=> v1_xboole_0(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.19/0.52  fof(f232,plain,(
% 0.19/0.52    k1_xboole_0 = sK1 | ~spl8_31),
% 0.19/0.52    inference(resolution,[],[f229,f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.52  fof(f229,plain,(
% 0.19/0.52    v1_xboole_0(sK1) | ~spl8_31),
% 0.19/0.52    inference(avatar_component_clause,[],[f228])).
% 0.19/0.52  fof(f231,plain,(
% 0.19/0.52    k1_xboole_0 != sK2 | k1_xboole_0 != sK7 | v1_xboole_0(sK2) | ~v1_xboole_0(sK7)),
% 0.19/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.52  fof(f230,plain,(
% 0.19/0.52    ~spl8_4 | spl8_31 | spl8_30),
% 0.19/0.52    inference(avatar_split_clause,[],[f225,f220,f228,f80])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    spl8_4 <=> m1_subset_1(sK5,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.19/0.52  fof(f220,plain,(
% 0.19/0.52    spl8_30 <=> r2_hidden(sK5,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.19/0.52  fof(f225,plain,(
% 0.19/0.52    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl8_30),
% 0.19/0.52    inference(resolution,[],[f221,f56])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.52    inference(flattening,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.52  fof(f221,plain,(
% 0.19/0.52    ~r2_hidden(sK5,sK1) | spl8_30),
% 0.19/0.52    inference(avatar_component_clause,[],[f220])).
% 0.19/0.52  fof(f223,plain,(
% 0.19/0.52    ~spl8_30 | ~spl8_17 | ~spl8_20 | spl8_26),
% 0.19/0.52    inference(avatar_split_clause,[],[f216,f190,f157,f141,f220])).
% 0.19/0.52  fof(f141,plain,(
% 0.19/0.52    spl8_17 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.19/0.52  fof(f157,plain,(
% 0.19/0.52    spl8_20 <=> ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    spl8_26 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.19/0.52  fof(f216,plain,(
% 0.19/0.52    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~r2_hidden(sK5,sK1) | (~spl8_20 | spl8_26)),
% 0.19/0.52    inference(resolution,[],[f207,f158])).
% 0.19/0.52  fof(f158,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,sK1)) ) | ~spl8_20),
% 0.19/0.52    inference(avatar_component_clause,[],[f157])).
% 0.19/0.52  fof(f207,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(X0,k1_relat_1(sK4))) ) | spl8_26),
% 0.19/0.52    inference(resolution,[],[f191,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f40])).
% 0.19/0.52  % (22728)Refutation not found, incomplete strategy% (22728)------------------------------
% 0.19/0.52  % (22728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (22728)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (22728)Memory used [KB]: 10746
% 0.19/0.52  % (22728)Time elapsed: 0.107 s
% 0.19/0.52  % (22728)------------------------------
% 0.19/0.52  % (22728)------------------------------
% 0.19/0.52  % (22732)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (22707)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(rectify,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(nnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.52  fof(f191,plain,(
% 0.19/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl8_26),
% 0.19/0.52    inference(avatar_component_clause,[],[f190])).
% 0.19/0.52  fof(f204,plain,(
% 0.19/0.52    ~spl8_5 | spl8_25),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f203])).
% 0.19/0.52  fof(f203,plain,(
% 0.19/0.52    $false | (~spl8_5 | spl8_25)),
% 0.19/0.52    inference(subsumption_resolution,[],[f85,f202])).
% 0.19/0.52  fof(f202,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl8_25),
% 0.19/0.52    inference(resolution,[],[f188,f64])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.52    inference(pure_predicate_removal,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.52  fof(f188,plain,(
% 0.19/0.52    ~v5_relat_1(sK4,sK0) | spl8_25),
% 0.19/0.52    inference(avatar_component_clause,[],[f187])).
% 0.19/0.52  fof(f187,plain,(
% 0.19/0.52    spl8_25 <=> v5_relat_1(sK4,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl8_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    spl8_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.19/0.52  fof(f201,plain,(
% 0.19/0.52    spl8_27),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f199])).
% 0.19/0.52  fof(f199,plain,(
% 0.19/0.52    $false | spl8_27),
% 0.19/0.52    inference(resolution,[],[f197,f55])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.52  fof(f197,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl8_27),
% 0.19/0.52    inference(avatar_component_clause,[],[f196])).
% 0.19/0.52  fof(f196,plain,(
% 0.19/0.52    spl8_27 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.19/0.52  fof(f198,plain,(
% 0.19/0.52    ~spl8_27 | ~spl8_5 | spl8_24),
% 0.19/0.52    inference(avatar_split_clause,[],[f194,f184,f84,f196])).
% 0.19/0.52  fof(f184,plain,(
% 0.19/0.52    spl8_24 <=> v1_relat_1(sK4)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.19/0.52  fof(f194,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl8_5 | spl8_24)),
% 0.19/0.52    inference(resolution,[],[f193,f85])).
% 0.19/0.52  fof(f193,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_24),
% 0.19/0.52    inference(resolution,[],[f185,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.52  fof(f185,plain,(
% 0.19/0.52    ~v1_relat_1(sK4) | spl8_24),
% 0.19/0.52    inference(avatar_component_clause,[],[f184])).
% 0.19/0.52  fof(f192,plain,(
% 0.19/0.52    ~spl8_24 | ~spl8_25 | ~spl8_6 | ~spl8_26 | spl8_23),
% 0.19/0.52    inference(avatar_split_clause,[],[f182,f178,f190,f88,f187,f184])).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    spl8_6 <=> v1_funct_1(sK4)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    spl8_23 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.19/0.52  fof(f182,plain,(
% 0.19/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl8_23),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f181])).
% 0.19/0.52  fof(f181,plain,(
% 0.19/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl8_23),
% 0.19/0.52    inference(superposition,[],[f179,f57])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl8_23),
% 0.19/0.52    inference(avatar_component_clause,[],[f178])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    ~spl8_23 | spl8_1 | ~spl8_22),
% 0.19/0.52    inference(avatar_split_clause,[],[f176,f172,f68,f178])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    spl8_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.19/0.52  fof(f172,plain,(
% 0.19/0.52    spl8_22 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.19/0.52  fof(f176,plain,(
% 0.19/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl8_1 | ~spl8_22)),
% 0.19/0.52    inference(superposition,[],[f69,f173])).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl8_22),
% 0.19/0.52    inference(avatar_component_clause,[],[f172])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl8_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f68])).
% 0.19/0.52  fof(f175,plain,(
% 0.19/0.52    ~spl8_18 | spl8_22 | ~spl8_6 | ~spl8_4 | ~spl8_5 | ~spl8_21),
% 0.19/0.52    inference(avatar_split_clause,[],[f169,f165,f84,f80,f88,f172,f145])).
% 0.19/0.52  fof(f145,plain,(
% 0.19/0.52    spl8_18 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.19/0.52  fof(f165,plain,(
% 0.19/0.52    spl8_21 <=> ! [X1,X0,X2] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(X2,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.19/0.52  fof(f169,plain,(
% 0.19/0.52    ~v1_funct_1(sK4) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | (~spl8_4 | ~spl8_5 | ~spl8_21)),
% 0.19/0.52    inference(resolution,[],[f168,f85])).
% 0.19/0.52  fof(f168,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))) ) | (~spl8_4 | ~spl8_21)),
% 0.19/0.52    inference(resolution,[],[f166,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    m1_subset_1(sK5,sK1) | ~spl8_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f80])).
% 0.19/0.52  fof(f166,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))) ) | ~spl8_21),
% 0.19/0.52    inference(avatar_component_clause,[],[f165])).
% 0.19/0.52  fof(f167,plain,(
% 0.19/0.52    spl8_10 | ~spl8_9 | ~spl8_7 | spl8_2 | spl8_21 | ~spl8_8 | ~spl8_16),
% 0.19/0.52    inference(avatar_split_clause,[],[f161,f135,f96,f165,f72,f92,f100,f104])).
% 0.19/0.52  fof(f104,plain,(
% 0.19/0.52    spl8_10 <=> v1_xboole_0(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.19/0.52  fof(f100,plain,(
% 0.19/0.52    spl8_9 <=> v1_funct_1(sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    spl8_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    spl8_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    spl8_16 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.19/0.52  fof(f161,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | k1_xboole_0 = sK1 | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | (~spl8_8 | ~spl8_16)),
% 0.19/0.52    inference(forward_demodulation,[],[f160,f136])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl8_16),
% 0.19/0.52    inference(avatar_component_clause,[],[f135])).
% 0.19/0.52  fof(f160,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | ~spl8_8),
% 0.19/0.52    inference(resolution,[],[f61,f97])).
% 0.19/0.52  fof(f97,plain,(
% 0.19/0.52    v1_funct_2(sK3,sK1,sK2) | ~spl8_8),
% 0.19/0.52    inference(avatar_component_clause,[],[f96])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.19/0.52    inference(flattening,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.19/0.52  % (22706)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  fof(f159,plain,(
% 0.19/0.52    ~spl8_9 | ~spl8_7 | spl8_19 | spl8_20 | ~spl8_8 | ~spl8_16),
% 0.19/0.52    inference(avatar_split_clause,[],[f150,f135,f96,f157,f154,f92,f100])).
% 0.19/0.52  fof(f154,plain,(
% 0.19/0.52    spl8_19 <=> k1_xboole_0 = sK2),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.19/0.52  fof(f150,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)) ) | (~spl8_8 | ~spl8_16)),
% 0.19/0.52    inference(forward_demodulation,[],[f149,f136])).
% 0.19/0.52  fof(f149,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) | ~v1_funct_1(sK3)) ) | ~spl8_8),
% 0.19/0.52    inference(resolution,[],[f65,f97])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_1(X3)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.52    inference(flattening,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.19/0.52  fof(f147,plain,(
% 0.19/0.52    spl8_18 | ~spl8_3 | ~spl8_16),
% 0.19/0.52    inference(avatar_split_clause,[],[f139,f135,f76,f145])).
% 0.19/0.52  fof(f76,plain,(
% 0.19/0.52    spl8_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | (~spl8_3 | ~spl8_16)),
% 0.19/0.52    inference(superposition,[],[f77,f136])).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl8_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f76])).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    spl8_17 | ~spl8_14 | ~spl8_16),
% 0.19/0.52    inference(avatar_split_clause,[],[f138,f135,f125,f141])).
% 0.19/0.52  fof(f125,plain,(
% 0.19/0.52    spl8_14 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl8_14 | ~spl8_16)),
% 0.19/0.52    inference(superposition,[],[f126,f136])).
% 0.19/0.52  fof(f126,plain,(
% 0.19/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl8_14),
% 0.19/0.52    inference(avatar_component_clause,[],[f125])).
% 0.19/0.52  fof(f137,plain,(
% 0.19/0.52    spl8_16 | ~spl8_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f129,f92,f135])).
% 0.19/0.52  fof(f129,plain,(
% 0.19/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl8_7),
% 0.19/0.52    inference(resolution,[],[f63,f93])).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f92])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.52  fof(f127,plain,(
% 0.19/0.52    ~spl8_5 | spl8_14 | ~spl8_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f122,f76,f125,f84])).
% 0.19/0.52  fof(f122,plain,(
% 0.19/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl8_3),
% 0.19/0.52    inference(superposition,[],[f77,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.52  fof(f115,plain,(
% 0.19/0.52    spl8_12 | ~spl8_11),
% 0.19/0.52    inference(avatar_split_clause,[],[f111,f108,f113])).
% 0.19/0.52  fof(f113,plain,(
% 0.19/0.52    spl8_12 <=> k1_xboole_0 = sK7),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    spl8_11 <=> v1_xboole_0(sK7)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    k1_xboole_0 = sK7 | ~spl8_11),
% 0.19/0.52    inference(resolution,[],[f54,f109])).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    v1_xboole_0(sK7) | ~spl8_11),
% 0.19/0.52    inference(avatar_component_clause,[],[f108])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    spl8_11),
% 0.19/0.52    inference(avatar_split_clause,[],[f66,f108])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    v1_xboole_0(sK7)),
% 0.19/0.52    inference(cnf_transformation,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    v1_xboole_0(sK7)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3,f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK7)),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ? [X0] : v1_xboole_0(X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    ~spl8_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f43,f104])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ~v1_xboole_0(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f35,f34,f33,f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.19/0.52    inference(flattening,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.19/0.52    inference(negated_conjecture,[],[f13])).
% 0.19/0.52  fof(f13,conjecture,(
% 0.19/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.19/0.52  fof(f102,plain,(
% 0.19/0.52    spl8_9),
% 0.19/0.52    inference(avatar_split_clause,[],[f44,f100])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    v1_funct_1(sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f98,plain,(
% 0.19/0.52    spl8_8),
% 0.19/0.52    inference(avatar_split_clause,[],[f45,f96])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    spl8_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f46,f92])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    spl8_6),
% 0.19/0.52    inference(avatar_split_clause,[],[f47,f88])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    v1_funct_1(sK4)),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    spl8_5),
% 0.19/0.52    inference(avatar_split_clause,[],[f48,f84])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f82,plain,(
% 0.19/0.52    spl8_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f49,f80])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    m1_subset_1(sK5,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    spl8_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f50,f76])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    ~spl8_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f51,f72])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    k1_xboole_0 != sK1),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ~spl8_1),
% 0.19/0.52    inference(avatar_split_clause,[],[f52,f68])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (22730)------------------------------
% 0.19/0.52  % (22730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (22730)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (22730)Memory used [KB]: 10874
% 0.19/0.52  % (22730)Time elapsed: 0.092 s
% 0.19/0.52  % (22730)------------------------------
% 0.19/0.52  % (22730)------------------------------
% 0.19/0.52  % (22703)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (22712)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (22711)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.53  % (22733)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (22702)Success in time 0.178 s
%------------------------------------------------------------------------------
