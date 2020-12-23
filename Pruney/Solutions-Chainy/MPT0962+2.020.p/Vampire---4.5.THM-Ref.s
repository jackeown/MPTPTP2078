%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 244 expanded)
%              Number of leaves         :   28 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  384 ( 801 expanded)
%              Number of equality atoms :   86 ( 179 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f137,f188,f206,f221,f234,f281,f287,f305,f318,f337,f364,f379,f384,f389,f410,f418])).

fof(f418,plain,
    ( spl4_35
    | ~ spl4_36
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | spl4_35
    | ~ spl4_36
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f416,f388])).

fof(f388,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl4_36
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f416,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_35
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f414,f383])).

fof(f383,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl4_35
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f414,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_38 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_38 ),
    inference(superposition,[],[f73,f409])).

fof(f409,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl4_38
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f73,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f410,plain,
    ( spl4_38
    | ~ spl4_34
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f394,f386,f376,f407])).

fof(f376,plain,
    ( spl4_34
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f394,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_34
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f392,f378])).

fof(f378,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f376])).

fof(f392,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_36 ),
    inference(resolution,[],[f388,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f389,plain,
    ( spl4_36
    | ~ spl4_1
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f374,f353,f334,f78,f386])).

fof(f78,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f334,plain,
    ( spl4_31
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f353,plain,
    ( spl4_32
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f374,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f336,f367])).

fof(f367,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f366,f80])).

fof(f80,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f366,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f365])).

fof(f365,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_32 ),
    inference(superposition,[],[f47,f355])).

fof(f355,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f353])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f336,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f384,plain,
    ( ~ spl4_35
    | ~ spl4_1
    | spl4_28
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f373,f353,f315,f78,f381])).

fof(f315,plain,
    ( spl4_28
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f373,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | spl4_28
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f317,f367])).

fof(f317,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f315])).

fof(f379,plain,
    ( spl4_34
    | ~ spl4_1
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f367,f353,f78,f376])).

fof(f364,plain,
    ( spl4_32
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f313,f302,f353])).

fof(f302,plain,
    ( spl4_27
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f313,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f312,f103])).

fof(f103,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f51,f93])).

fof(f93,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f312,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl4_27 ),
    inference(resolution,[],[f304,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f304,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f302])).

fof(f337,plain,
    ( spl4_31
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f327,f278,f134,f334])).

fof(f134,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f278,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f327,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f135,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f278])).

fof(f135,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f318,plain,
    ( ~ spl4_28
    | spl4_5
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f292,f278,f130,f315])).

fof(f130,plain,
    ( spl4_5
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f292,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl4_5
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f132,f280])).

fof(f132,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f305,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f291,f278,f88,f302])).

fof(f88,plain,
    ( spl4_3
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f291,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f90,f280])).

fof(f90,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f287,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f80,f90,f68,f136,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f281,plain,
    ( ~ spl4_6
    | spl4_26
    | spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f241,f231,f130,f278,f134])).

fof(f231,plain,
    ( spl4_20
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f241,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f240,f132])).

fof(f240,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_20 ),
    inference(superposition,[],[f63,f233])).

fof(f233,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f234,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f222,f219,f88,f231])).

fof(f219,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f222,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(resolution,[],[f220,f90])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( spl4_18
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f215,f204,f219])).

fof(f204,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK1),X1)
        | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1) )
    | ~ spl4_15 ),
    inference(resolution,[],[f205,f68])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK1),X1)
        | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl4_15
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f193,f186,f204])).

fof(f186,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | ~ r1_tarski(k2_relat_1(sK1),X1)
        | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1) )
    | ~ spl4_13 ),
    inference(resolution,[],[f187,f60])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK1),X1)
        | ~ r1_tarski(k2_relat_1(sK1),X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl4_13
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f143,f78,f186])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f59,f80])).

fof(f137,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f128,f83,f134,f130])).

fof(f83,plain,
    ( spl4_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f43,f85])).

fof(f85,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f43,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

% (29977)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f91,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f42,f88])).

fof(f42,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (29969)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (29991)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (29986)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (29973)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (29988)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (29981)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (29968)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (29979)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (29985)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (29974)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (29980)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29972)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (29976)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (29970)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (29972)Refutation not found, incomplete strategy% (29972)------------------------------
% 0.21/0.50  % (29972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29967)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (29972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29972)Memory used [KB]: 6140
% 0.21/0.50  % (29972)Time elapsed: 0.058 s
% 0.21/0.50  % (29972)------------------------------
% 0.21/0.50  % (29972)------------------------------
% 0.21/0.51  % (29968)Refutation not found, incomplete strategy% (29968)------------------------------
% 0.21/0.51  % (29968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29968)Memory used [KB]: 10618
% 0.21/0.51  % (29968)Time elapsed: 0.099 s
% 0.21/0.51  % (29968)------------------------------
% 0.21/0.51  % (29968)------------------------------
% 0.21/0.51  % (29971)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (29980)Refutation not found, incomplete strategy% (29980)------------------------------
% 0.21/0.51  % (29980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29980)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29980)Memory used [KB]: 6268
% 0.21/0.51  % (29980)Time elapsed: 0.060 s
% 0.21/0.51  % (29980)------------------------------
% 0.21/0.51  % (29980)------------------------------
% 0.21/0.51  % (29969)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f81,f86,f91,f137,f188,f206,f221,f234,f281,f287,f305,f318,f337,f364,f379,f384,f389,f410,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    spl4_35 | ~spl4_36 | ~spl4_38),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    $false | (spl4_35 | ~spl4_36 | ~spl4_38)),
% 0.21/0.51    inference(subsumption_resolution,[],[f416,f388])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f386])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    spl4_36 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_35 | ~spl4_38)),
% 0.21/0.51    inference(subsumption_resolution,[],[f414,f383])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | spl4_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f381])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    spl4_35 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.51  fof(f414,plain,(
% 0.21/0.51    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_38),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f412])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_38),
% 0.21/0.51    inference(superposition,[],[f73,f409])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl4_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f407])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl4_38 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    spl4_38 | ~spl4_34 | ~spl4_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f394,f386,f376,f407])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    spl4_34 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_34 | ~spl4_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f392,f378])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK1) | ~spl4_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f376])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl4_36),
% 0.21/0.51    inference(resolution,[],[f388,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    spl4_36 | ~spl4_1 | ~spl4_31 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f374,f353,f334,f78,f386])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl4_1 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    spl4_31 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    spl4_32 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_31 | ~spl4_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f336,f367])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK1) | (~spl4_1 | ~spl4_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f366,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl4_32),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f365])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl4_32),
% 0.21/0.51    inference(superposition,[],[f47,f355])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK1) | ~spl4_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f353])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | ~spl4_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f334])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    ~spl4_35 | ~spl4_1 | spl4_28 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f373,f353,f315,f78,f381])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    spl4_28 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl4_1 | spl4_28 | ~spl4_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f317,f367])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f315])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    spl4_34 | ~spl4_1 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f367,f353,f78,f376])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    spl4_32 | ~spl4_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f313,f302,f353])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    spl4_27 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK1) | ~spl4_27),
% 0.21/0.51    inference(subsumption_resolution,[],[f312,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 0.21/0.51    inference(superposition,[],[f51,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f52,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | ~spl4_27),
% 0.21/0.51    inference(resolution,[],[f304,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl4_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f302])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    spl4_31 | ~spl4_6 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f327,f278,f134,f334])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    spl4_26 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | (~spl4_6 | ~spl4_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f135,f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    ~spl4_28 | spl4_5 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f292,f278,f130,f315])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl4_5 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl4_5 | ~spl4_26)),
% 0.21/0.51    inference(backward_demodulation,[],[f132,f280])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f130])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    spl4_27 | ~spl4_3 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f291,f278,f88,f302])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl4_3 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl4_3 | ~spl4_26)),
% 0.21/0.51    inference(backward_demodulation,[],[f90,f280])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK1),sK0) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_3 | spl4_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    $false | (~spl4_1 | ~spl4_3 | spl4_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f80,f90,f68,f136,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    ~spl4_6 | spl4_26 | spl4_5 | ~spl4_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f241,f231,f130,f278,f134])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl4_20 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (spl4_5 | ~spl4_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f240,f132])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_20),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    k1_relat_1(sK1) != k1_relat_1(sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_20),
% 0.21/0.51    inference(superposition,[],[f63,f233])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl4_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f231])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    spl4_20 | ~spl4_3 | ~spl4_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f222,f219,f88,f231])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl4_18 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | (~spl4_3 | ~spl4_18)),
% 0.21/0.51    inference(resolution,[],[f220,f90])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1)) ) | ~spl4_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f219])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl4_18 | ~spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f215,f204,f219])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    spl4_15 <=> ! [X1,X0] : (~r1_tarski(k1_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK1),X1) | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),X0,sK1)) ) | ~spl4_15),
% 0.21/0.51    inference(resolution,[],[f205,f68])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK1),X1) | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1)) ) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f204])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl4_15 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f193,f186,f204])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl4_13 <=> ! [X1,X0] : (~r1_tarski(k2_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | ~r1_tarski(k2_relat_1(sK1),X1) | k1_relat_1(sK1) = k1_relset_1(X0,X1,sK1)) ) | ~spl4_13),
% 0.21/0.51    inference(resolution,[],[f187,f60])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK1),X1) | ~r1_tarski(k2_relat_1(sK1),X0)) ) | ~spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f186])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl4_13 | ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f78,f186])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl4_1),
% 0.21/0.51    inference(resolution,[],[f59,f80])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~spl4_5 | ~spl4_6 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f128,f83,f134,f130])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl4_2 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl4_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f43,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  % (29977)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f88])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f83])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f78])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29969)------------------------------
% 0.21/0.51  % (29969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29969)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29969)Memory used [KB]: 6396
% 0.21/0.51  % (29969)Time elapsed: 0.094 s
% 0.21/0.51  % (29969)------------------------------
% 0.21/0.51  % (29969)------------------------------
% 0.21/0.51  % (29966)Success in time 0.148 s
%------------------------------------------------------------------------------
