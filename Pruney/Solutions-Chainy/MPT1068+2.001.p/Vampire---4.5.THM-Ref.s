%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 377 expanded)
%              Number of leaves         :   53 ( 178 expanded)
%              Depth                    :    9
%              Number of atoms          :  670 (1889 expanded)
%              Number of equality atoms :  131 ( 418 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f110,f114,f118,f122,f126,f130,f148,f155,f171,f181,f188,f224,f228,f245,f279,f296,f304,f314,f318,f325,f335,f351,f421,f438,f482,f495,f500,f504,f517,f519])).

fof(f519,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f517,plain,
    ( spl6_66
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f506,f490,f515])).

fof(f515,plain,
    ( spl6_66
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f490,plain,
    ( spl6_61
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f506,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_61 ),
    inference(resolution,[],[f491,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f491,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f490])).

fof(f504,plain,
    ( ~ spl6_47
    | spl6_63 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl6_47
    | spl6_63 ),
    inference(subsumption_resolution,[],[f350,f501])).

fof(f501,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl6_63 ),
    inference(resolution,[],[f499,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f499,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK1)
    | spl6_63 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl6_63
  <=> v4_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f350,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl6_47
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f500,plain,
    ( ~ spl6_53
    | ~ spl6_63
    | spl6_62 ),
    inference(avatar_split_clause,[],[f496,f493,f498,f427])).

fof(f427,plain,
    ( spl6_53
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f493,plain,
    ( spl6_62
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f496,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK1)
    | ~ v1_relat_1(k1_xboole_0)
    | spl6_62 ),
    inference(resolution,[],[f494,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f494,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK1)
    | spl6_62 ),
    inference(avatar_component_clause,[],[f493])).

fof(f495,plain,
    ( spl6_61
    | ~ spl6_62
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f484,f480,f493,f490])).

fof(f480,plain,
    ( spl6_59
  <=> r1_xboole_0(k1_relat_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f484,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK1)
    | v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_59 ),
    inference(resolution,[],[f481,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f481,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK1)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f480])).

fof(f482,plain,
    ( spl6_59
    | ~ spl6_19
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f478,f349,f179,f480])).

fof(f179,plain,
    ( spl6_19
  <=> ! [X2] :
        ( ~ v4_relat_1(k1_xboole_0,X2)
        | r1_xboole_0(k1_relat_1(k1_xboole_0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f478,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK1)
    | ~ spl6_19
    | ~ spl6_47 ),
    inference(resolution,[],[f471,f350])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r1_xboole_0(k1_relat_1(k1_xboole_0),X0) )
    | ~ spl6_19 ),
    inference(resolution,[],[f180,f77])).

fof(f180,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(k1_xboole_0,X2)
        | r1_xboole_0(k1_relat_1(k1_xboole_0),X2) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f438,plain,
    ( k1_xboole_0 != sK3
    | v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f421,plain,
    ( ~ spl6_18
    | ~ spl6_47 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_47 ),
    inference(resolution,[],[f350,f177])).

fof(f177,plain,
    ( ! [X4,X3] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_18
  <=> ! [X3,X4] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f351,plain,
    ( spl6_47
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f347,f276,f222,f349])).

fof(f222,plain,
    ( spl6_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f276,plain,
    ( spl6_34
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f347,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f223,f277])).

fof(f277,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f276])).

fof(f223,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f335,plain,
    ( spl6_2
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f327,f323,f96])).

fof(f96,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f323,plain,
    ( spl6_41
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f327,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_41 ),
    inference(resolution,[],[f324,f63])).

fof(f324,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f323])).

fof(f325,plain,
    ( ~ spl6_4
    | spl6_41
    | spl6_40 ),
    inference(avatar_split_clause,[],[f320,f312,f323,f104])).

fof(f104,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f312,plain,
    ( spl6_40
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f320,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl6_40 ),
    inference(resolution,[],[f313,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f313,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f312])).

fof(f318,plain,
    ( ~ spl6_5
    | spl6_39 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl6_5
    | spl6_39 ),
    inference(subsumption_resolution,[],[f109,f315])).

fof(f315,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_39 ),
    inference(resolution,[],[f310,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f310,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_39
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f314,plain,
    ( ~ spl6_15
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_6
    | ~ spl6_40
    | ~ spl6_14
    | spl6_38 ),
    inference(avatar_split_clause,[],[f307,f302,f152,f312,f112,f309,f124,f159])).

fof(f159,plain,
    ( spl6_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f124,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f112,plain,
    ( spl6_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f152,plain,
    ( spl6_14
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f302,plain,
    ( spl6_38
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f307,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_14
    | spl6_38 ),
    inference(forward_demodulation,[],[f306,f153])).

fof(f153,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f306,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_38 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_38 ),
    inference(superposition,[],[f303,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

% (20639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f303,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f302])).

fof(f304,plain,
    ( ~ spl6_38
    | spl6_1
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f300,f293,f92,f302])).

fof(f92,plain,
    ( spl6_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f293,plain,
    ( spl6_36
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f300,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_1
    | ~ spl6_36 ),
    inference(superposition,[],[f93,f294])).

fof(f294,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f93,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f296,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | spl6_36
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f291,f241,f293,f108,f112,f116,f124])).

fof(f116,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f241,plain,
    ( spl6_30
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f291,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl6_30 ),
    inference(superposition,[],[f85,f242])).

fof(f242,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f279,plain,
    ( spl6_34
    | spl6_2
    | ~ spl6_27
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f273,f222,f226,f96,f276])).

fof(f226,plain,
    ( spl6_27
  <=> v1_funct_2(sK3,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f273,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ spl6_26 ),
    inference(resolution,[],[f223,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f245,plain,
    ( spl6_30
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_7
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f239,f186,f116,f124,f120,f100,f241])).

fof(f100,plain,
    ( spl6_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f120,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f186,plain,
    ( spl6_20
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f239,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_7
    | ~ spl6_20 ),
    inference(resolution,[],[f187,f117])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4))
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f228,plain,
    ( spl6_27
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f206,f143,f120,f226])).

fof(f143,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f206,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(superposition,[],[f121,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f121,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f224,plain,
    ( spl6_26
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f205,f143,f116,f222])).

fof(f205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(superposition,[],[f117,f144])).

% (20640)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f188,plain,
    ( ~ spl6_6
    | spl6_20
    | spl6_12
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f182,f108,f143,f186,f112])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = sK2
        | ~ r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4))
        | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_2(X1,X0,sK2)
        | ~ v1_funct_1(X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f84,f109])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f181,plain,
    ( spl6_18
    | spl6_19
    | spl6_18 ),
    inference(avatar_split_clause,[],[f174,f176,f179,f176])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v4_relat_1(k1_xboole_0,X2)
      | r1_xboole_0(k1_relat_1(k1_xboole_0),X2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v4_relat_1(X0,X1)
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f138,f75])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v4_relat_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f131,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k7_relat_1(X0,X1)
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f67,f75])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f171,plain,
    ( ~ spl6_7
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl6_7
    | spl6_15 ),
    inference(subsumption_resolution,[],[f117,f169])).

fof(f169,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_15 ),
    inference(resolution,[],[f160,f75])).

fof(f160,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f155,plain,
    ( ~ spl6_7
    | spl6_14
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f150,f146,f152,f116])).

fof(f146,plain,
    ( spl6_13
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f150,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_13 ),
    inference(superposition,[],[f76,f147])).

fof(f147,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f148,plain,
    ( ~ spl6_7
    | spl6_12
    | spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f140,f120,f146,f143,f116])).

fof(f140,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(resolution,[],[f78,f121])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f52,f128])).

fof(f128,plain,
    ( spl6_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f52,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f47,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
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

fof(f45,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
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
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

% (20636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f16,conjecture,(
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

fof(f126,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f56,f112])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f58,f104])).

fof(f58,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f59,f100])).

fof(f59,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f60,f96])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f61,f92])).

fof(f61,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:58:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (20648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (20648)Refutation not found, incomplete strategy% (20648)------------------------------
% 0.21/0.46  % (20648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (20648)Memory used [KB]: 6268
% 0.21/0.46  % (20648)Time elapsed: 0.029 s
% 0.21/0.46  % (20648)------------------------------
% 0.21/0.46  % (20648)------------------------------
% 0.21/0.48  % (20642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (20641)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (20649)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (20647)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (20642)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f520,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f110,f114,f118,f122,f126,f130,f148,f155,f171,f181,f188,f224,f228,f245,f279,f296,f304,f314,f318,f325,f335,f351,f421,f438,f482,f495,f500,f504,f517,f519])).
% 0.21/0.49  fof(f519,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    spl6_66 | ~spl6_61),
% 0.21/0.49    inference(avatar_split_clause,[],[f506,f490,f515])).
% 0.21/0.49  fof(f515,plain,(
% 0.21/0.49    spl6_66 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.21/0.49  fof(f490,plain,(
% 0.21/0.49    spl6_61 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.21/0.49  fof(f506,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_61),
% 0.21/0.49    inference(resolution,[],[f491,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f491,plain,(
% 0.21/0.49    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl6_61),
% 0.21/0.49    inference(avatar_component_clause,[],[f490])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    ~spl6_47 | spl6_63),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f503])).
% 0.21/0.49  fof(f503,plain,(
% 0.21/0.49    $false | (~spl6_47 | spl6_63)),
% 0.21/0.49    inference(subsumption_resolution,[],[f350,f501])).
% 0.21/0.49  fof(f501,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl6_63),
% 0.21/0.49    inference(resolution,[],[f499,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f499,plain,(
% 0.21/0.49    ~v4_relat_1(k1_xboole_0,sK1) | spl6_63),
% 0.21/0.49    inference(avatar_component_clause,[],[f498])).
% 0.21/0.49  fof(f498,plain,(
% 0.21/0.49    spl6_63 <=> v4_relat_1(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f349])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    spl6_47 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.49  fof(f500,plain,(
% 0.21/0.49    ~spl6_53 | ~spl6_63 | spl6_62),
% 0.21/0.49    inference(avatar_split_clause,[],[f496,f493,f498,f427])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    spl6_53 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.49  fof(f493,plain,(
% 0.21/0.49    spl6_62 <=> r1_tarski(k1_relat_1(k1_xboole_0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.21/0.49  fof(f496,plain,(
% 0.21/0.49    ~v4_relat_1(k1_xboole_0,sK1) | ~v1_relat_1(k1_xboole_0) | spl6_62),
% 0.21/0.49    inference(resolution,[],[f494,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f494,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k1_xboole_0),sK1) | spl6_62),
% 0.21/0.49    inference(avatar_component_clause,[],[f493])).
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    spl6_61 | ~spl6_62 | ~spl6_59),
% 0.21/0.49    inference(avatar_split_clause,[],[f484,f480,f493,f490])).
% 0.21/0.49  fof(f480,plain,(
% 0.21/0.49    spl6_59 <=> r1_xboole_0(k1_relat_1(k1_xboole_0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.49  fof(f484,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k1_xboole_0),sK1) | v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl6_59),
% 0.21/0.49    inference(resolution,[],[f481,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.49  fof(f481,plain,(
% 0.21/0.49    r1_xboole_0(k1_relat_1(k1_xboole_0),sK1) | ~spl6_59),
% 0.21/0.49    inference(avatar_component_clause,[],[f480])).
% 0.21/0.49  fof(f482,plain,(
% 0.21/0.49    spl6_59 | ~spl6_19 | ~spl6_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f478,f349,f179,f480])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl6_19 <=> ! [X2] : (~v4_relat_1(k1_xboole_0,X2) | r1_xboole_0(k1_relat_1(k1_xboole_0),X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f478,plain,(
% 0.21/0.49    r1_xboole_0(k1_relat_1(k1_xboole_0),sK1) | (~spl6_19 | ~spl6_47)),
% 0.21/0.49    inference(resolution,[],[f471,f350])).
% 0.21/0.49  fof(f471,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) ) | ~spl6_19),
% 0.21/0.49    inference(resolution,[],[f180,f77])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X2] : (~v4_relat_1(k1_xboole_0,X2) | r1_xboole_0(k1_relat_1(k1_xboole_0),X2)) ) | ~spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f179])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    k1_xboole_0 != sK3 | v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK3)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    ~spl6_18 | ~spl6_47),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f419])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    $false | (~spl6_18 | ~spl6_47)),
% 0.21/0.49    inference(resolution,[],[f350,f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl6_18 <=> ! [X3,X4] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    spl6_47 | ~spl6_26 | ~spl6_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f347,f276,f222,f349])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl6_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl6_34 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_26 | ~spl6_34)),
% 0.21/0.49    inference(forward_demodulation,[],[f223,f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl6_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f276])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f222])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    spl6_2 | ~spl6_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f327,f323,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    spl6_41 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_41),
% 0.21/0.49    inference(resolution,[],[f324,f63])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl6_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f323])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ~spl6_4 | spl6_41 | spl6_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f320,f312,f323,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl6_40 <=> r2_hidden(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl6_40),
% 0.21/0.49    inference(resolution,[],[f313,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~r2_hidden(sK5,sK1) | spl6_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f312])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~spl6_5 | spl6_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    $false | (~spl6_5 | spl6_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f315])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_39),
% 0.21/0.49    inference(resolution,[],[f310,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ~v1_relat_1(sK4) | spl6_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f309])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    spl6_39 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~spl6_15 | ~spl6_9 | ~spl6_39 | ~spl6_6 | ~spl6_40 | ~spl6_14 | spl6_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f307,f302,f152,f312,f112,f309,f124,f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl6_15 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl6_9 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_6 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl6_14 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    spl6_38 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~r2_hidden(sK5,sK1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl6_14 | spl6_38)),
% 0.21/0.49    inference(forward_demodulation,[],[f306,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_38),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f305])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_38),
% 0.21/0.49    inference(superposition,[],[f303,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.49  % (20639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl6_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f302])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~spl6_38 | spl6_1 | ~spl6_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f300,f293,f92,f302])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl6_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl6_36 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl6_1 | ~spl6_36)),
% 0.21/0.49    inference(superposition,[],[f93,f294])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl6_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f293])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~spl6_9 | ~spl6_7 | ~spl6_6 | ~spl6_5 | spl6_36 | ~spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f291,f241,f293,f108,f112,f116,f124])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    spl6_30 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | ~spl6_30),
% 0.21/0.49    inference(superposition,[],[f85,f242])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f241])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.49    inference(flattening,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    spl6_34 | spl6_2 | ~spl6_27 | ~spl6_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f273,f222,f226,f96,f276])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl6_27 <=> v1_funct_2(sK3,sK1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~spl6_26),
% 0.21/0.49    inference(resolution,[],[f223,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl6_30 | ~spl6_3 | ~spl6_8 | ~spl6_9 | ~spl6_7 | ~spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f239,f186,f116,f124,f120,f100,f241])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl6_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl6_20 <=> ! [X1,X0] : (~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_7 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f187,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK2) | ~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4)) | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4)) ) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    spl6_27 | ~spl6_8 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f206,f143,f120,f226])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl6_12 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,k1_xboole_0) | (~spl6_8 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f121,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl6_26 | ~spl6_7 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f205,f143,f116,f222])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_7 | ~spl6_12)),
% 0.21/0.49    inference(superposition,[],[f117,f144])).
% 0.21/0.49  % (20640)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~spl6_6 | spl6_20 | spl6_12 | ~spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f108,f143,f186,f112])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(X0,sK2,X1),k1_relset_1(sK2,sK0,sK4)) | k8_funct_2(X0,sK2,sK0,X1,sK4) = k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_2(X1,X0,sK2) | ~v1_funct_1(X1)) ) | ~spl6_5),
% 0.21/0.49    inference(resolution,[],[f84,f109])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl6_18 | spl6_19 | spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f176,f179,f176])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(k1_xboole_0,X2) | r1_xboole_0(k1_relat_1(k1_xboole_0),X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v4_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.21/0.49    inference(resolution,[],[f138,f75])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r1_xboole_0(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v4_relat_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(superposition,[],[f131,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k7_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.49    inference(resolution,[],[f67,f75])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~spl6_7 | spl6_15),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    $false | (~spl6_7 | spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_15),
% 0.21/0.49    inference(resolution,[],[f160,f75])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~spl6_7 | spl6_14 | ~spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f150,f146,f152,f116])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl6_13 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_13),
% 0.21/0.49    inference(superposition,[],[f76,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~spl6_7 | spl6_12 | spl6_13 | ~spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f120,f146,f143,f116])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.21/0.49    inference(resolution,[],[f78,f121])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl6_10 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f47,f46,f45,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k1_funct_1(X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k1_funct_1(sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  % (20636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f124])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f120])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f116])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f112])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f108])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f104])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK5,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f100])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f96])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f92])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20642)------------------------------
% 0.21/0.49  % (20642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20642)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20642)Memory used [KB]: 11129
% 0.21/0.49  % (20642)Time elapsed: 0.043 s
% 0.21/0.49  % (20642)------------------------------
% 0.21/0.49  % (20642)------------------------------
% 0.21/0.50  % (20632)Success in time 0.136 s
%------------------------------------------------------------------------------
