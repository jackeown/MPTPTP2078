%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 208 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  410 ( 655 expanded)
%              Number of equality atoms :   51 (  98 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f120,f187,f192,f197,f252,f268,f276,f284,f291])).

fof(f291,plain,
    ( ~ spl6_9
    | spl6_14
    | ~ spl6_15
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl6_9
    | spl6_14
    | ~ spl6_15
    | spl6_23 ),
    inference(subsumption_resolution,[],[f289,f160])).

fof(f160,plain,
    ( k1_xboole_0 != sK2
    | spl6_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f289,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_9
    | ~ spl6_15
    | spl6_23 ),
    inference(subsumption_resolution,[],[f288,f119])).

fof(f119,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f288,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_15
    | spl6_23 ),
    inference(subsumption_resolution,[],[f286,f267])).

fof(f267,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl6_23
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f286,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_15 ),
    inference(superposition,[],[f151,f167])).

fof(f167,plain,
    ( sK0 = sK4(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_15
  <=> sK0 = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f151,plain,(
    ! [X5] :
      ( r2_hidden(sK4(X5),k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = X5 ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X5] :
      ( k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | r2_hidden(sK4(X5),k1_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f284,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(avatar_split_clause,[],[f283,f159,f117,f84,f165])).

fof(f84,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f283,plain,
    ( sK0 = sK4(sK2)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(subsumption_resolution,[],[f282,f119])).

fof(f282,plain,
    ( sK0 = sK4(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_3
    | spl6_14 ),
    inference(subsumption_resolution,[],[f281,f160])).

fof(f281,plain,
    ( sK0 = sK4(sK2)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f128,f61])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl6_3 ),
    inference(resolution,[],[f51,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f276,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f270,f84,f123])).

% (15414)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f123,plain,
    ( spl6_10
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f270,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f268,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_23
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f263,f94,f74,f265,f123,f117])).

fof(f74,plain,
    ( spl6_1
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f94,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f263,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f262,f96])).

fof(f96,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f262,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(resolution,[],[f76,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f76,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f252,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_2
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f248,f69])).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f248,plain,
    ( v1_xboole_0(k1_tarski(sK0))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(resolution,[],[f244,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f244,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f243,f108])).

fof(f108,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f243,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | spl6_2
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f242,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) )
    | spl6_2
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f241,f196])).

fof(f196,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_19
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0) )
    | spl6_2
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f240,f191])).

fof(f191,plain,
    ( v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_18
  <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl6_2
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f239,f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f239,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl6_17 ),
    inference(resolution,[],[f220,f186])).

fof(f186,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_17
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f197,plain,
    ( spl6_19
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f172,f159,f94,f194])).

fof(f172,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f96,f161])).

fof(f161,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f192,plain,
    ( spl6_18
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f171,f159,f89,f189])).

fof(f89,plain,
    ( spl6_4
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f171,plain,
    ( v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f91,f161])).

fof(f91,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f187,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f170,f159,f84,f184])).

fof(f170,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f86,f161])).

fof(f120,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f115,f84,f117])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f68,f86])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f66,f99])).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f97,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f92,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f49,f79])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f50,f74])).

fof(f50,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (15397)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15399)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (15398)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (15412)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (15407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (15405)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (15406)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (15405)Refutation not found, incomplete strategy% (15405)------------------------------
% 0.21/0.54  % (15405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15405)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15405)Memory used [KB]: 1791
% 0.21/0.54  % (15405)Time elapsed: 0.117 s
% 0.21/0.54  % (15405)------------------------------
% 0.21/0.54  % (15405)------------------------------
% 0.21/0.54  % (15412)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f120,f187,f192,f197,f252,f268,f276,f284,f291])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ~spl6_9 | spl6_14 | ~spl6_15 | spl6_23),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    $false | (~spl6_9 | spl6_14 | ~spl6_15 | spl6_23)),
% 0.21/0.54    inference(subsumption_resolution,[],[f289,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    k1_xboole_0 != sK2 | spl6_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f159])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl6_14 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | (~spl6_9 | ~spl6_15 | spl6_23)),
% 0.21/0.54    inference(subsumption_resolution,[],[f288,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl6_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl6_9 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl6_15 | spl6_23)),
% 0.21/0.54    inference(subsumption_resolution,[],[f286,f267])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl6_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f265])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    spl6_23 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl6_15),
% 0.21/0.54    inference(superposition,[],[f151,f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    sK0 = sK4(sK2) | ~spl6_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f165])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    spl6_15 <=> sK0 = sK4(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK4(X5),k1_relat_1(X5)) | ~v1_relat_1(X5) | k1_xboole_0 = X5) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X5] : (k1_xboole_0 = X5 | ~v1_relat_1(X5) | r2_hidden(sK4(X5),k1_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 0.21/0.54    inference(resolution,[],[f61,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    spl6_15 | ~spl6_3 | ~spl6_9 | spl6_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f283,f159,f117,f84,f165])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    sK0 = sK4(sK2) | (~spl6_3 | ~spl6_9 | spl6_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f282,f119])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    sK0 = sK4(sK2) | ~v1_relat_1(sK2) | (~spl6_3 | spl6_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f281,f160])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    sK0 = sK4(sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl6_3),
% 0.21/0.54    inference(resolution,[],[f128,f61])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl6_3),
% 0.21/0.54    inference(resolution,[],[f51,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl6_3),
% 0.21/0.54    inference(resolution,[],[f59,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f84])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    spl6_10 | ~spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f270,f84,f123])).
% 0.21/0.54  % (15414)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl6_10 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    v5_relat_1(sK2,sK1) | ~spl6_3),
% 0.21/0.54    inference(resolution,[],[f86,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ~spl6_9 | ~spl6_10 | ~spl6_23 | spl6_1 | ~spl6_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f263,f94,f74,f265,f123,f117])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl6_1 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl6_5 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (spl6_1 | ~spl6_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f262,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    v1_funct_1(sK2) | ~spl6_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl6_1),
% 0.21/0.54    inference(resolution,[],[f76,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f74])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    spl6_2 | ~spl6_6 | ~spl6_17 | ~spl6_18 | ~spl6_19),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    $false | (spl6_2 | ~spl6_6 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    v1_xboole_0(k1_tarski(sK0)) | (spl6_2 | ~spl6_6 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 0.21/0.54    inference(resolution,[],[f244,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) ) | (spl6_2 | ~spl6_6 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f243,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f57,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK0))) ) | (spl6_2 | ~spl6_6 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 0.21/0.54    inference(forward_demodulation,[],[f242,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl6_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))) ) | (spl6_2 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f241,f196])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0) | ~spl6_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    spl6_19 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0)) ) | (spl6_2 | ~spl6_17 | ~spl6_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f240,f191])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | ~spl6_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f189])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    spl6_18 <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | (spl6_2 | ~spl6_17)),
% 0.21/0.55    inference(subsumption_resolution,[],[f239,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | ~spl6_17),
% 0.21/0.55    inference(resolution,[],[f220,f186])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl6_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    spl6_17 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f219])).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X2,X3),k2_relat_1(X2)) | k1_xboole_0 = X1 | ~r2_hidden(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(superposition,[],[f54,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    spl6_19 | ~spl6_5 | ~spl6_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f172,f159,f94,f194])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    v1_funct_1(k1_xboole_0) | (~spl6_5 | ~spl6_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f96,f161])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | ~spl6_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f159])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl6_18 | ~spl6_4 | ~spl6_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f171,f159,f89,f189])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl6_4 <=> v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | (~spl6_4 | ~spl6_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f91,f161])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f89])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    spl6_17 | ~spl6_3 | ~spl6_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f170,f159,f84,f184])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | (~spl6_3 | ~spl6_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f86,f161])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl6_9 | ~spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f115,f84,f117])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    v1_relat_1(sK2) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f68,f86])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    spl6_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f66,f99])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl6_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f46,f94])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    v1_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f18])).
% 0.21/0.55  fof(f18,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f47,f89])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f48,f84])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f49,f79])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ~spl6_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f50,f74])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (15412)------------------------------
% 0.21/0.55  % (15412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15412)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (15412)Memory used [KB]: 6396
% 0.21/0.55  % (15412)Time elapsed: 0.131 s
% 0.21/0.55  % (15412)------------------------------
% 0.21/0.55  % (15412)------------------------------
% 0.21/0.55  % (15413)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (15416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (15395)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (15396)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (15415)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (15391)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (15401)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (15390)Success in time 0.196 s
%------------------------------------------------------------------------------
