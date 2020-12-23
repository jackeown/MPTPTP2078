%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:56 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 284 expanded)
%              Number of leaves         :   38 ( 129 expanded)
%              Depth                    :    9
%              Number of atoms          :  530 ( 949 expanded)
%              Number of equality atoms :   62 (  94 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f110,f119,f124,f134,f140,f145,f152,f169,f175,f185,f191,f194,f222,f225,f279,f281,f291,f309,f312])).

fof(f312,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_32
    | ~ spl2_20
    | spl2_36 ),
    inference(avatar_split_clause,[],[f311,f306,f188,f276,f131,f77,f107])).

fof(f107,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f77,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f131,plain,
    ( spl2_10
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f276,plain,
    ( spl2_32
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f188,plain,
    ( spl2_20
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f306,plain,
    ( spl2_36
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f311,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_20
    | spl2_36 ),
    inference(forward_demodulation,[],[f310,f189])).

fof(f189,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f310,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_36 ),
    inference(superposition,[],[f308,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f308,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f309,plain,
    ( ~ spl2_18
    | ~ spl2_23
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_36
    | spl2_33 ),
    inference(avatar_split_clause,[],[f292,f288,f306,f92,f77,f215,f178])).

fof(f178,plain,
    ( spl2_18
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f215,plain,
    ( spl2_23
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f92,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f288,plain,
    ( spl2_33
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f292,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_33 ),
    inference(superposition,[],[f290,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f290,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f288])).

fof(f291,plain,
    ( ~ spl2_33
    | spl2_7
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f282,f166,f116,f288])).

fof(f116,plain,
    ( spl2_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f166,plain,
    ( spl2_16
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f282,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_7
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f118,f168])).

fof(f168,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f118,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f281,plain,(
    spl2_32 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl2_32 ),
    inference(unit_resulting_resolution,[],[f72,f278,f75])).

% (14926)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f278,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f279,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_32
    | ~ spl2_13
    | spl2_24 ),
    inference(avatar_split_clause,[],[f245,f219,f149,f276,f131,f77,f107])).

fof(f149,plain,
    ( spl2_13
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f219,plain,
    ( spl2_24
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f245,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_13
    | spl2_24 ),
    inference(forward_demodulation,[],[f244,f151])).

fof(f151,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f244,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_24 ),
    inference(superposition,[],[f221,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f221,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f225,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_19
    | spl2_23 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_19
    | spl2_23 ),
    inference(unit_resulting_resolution,[],[f79,f133,f84,f94,f183,f217,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f217,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f183,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl2_19
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f84,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f133,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f79,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f222,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_23
    | ~ spl2_24
    | spl2_17 ),
    inference(avatar_split_clause,[],[f176,f172,f219,f215,f178,f92,f77])).

fof(f172,plain,
    ( spl2_17
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f176,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl2_17 ),
    inference(superposition,[],[f174,f70])).

fof(f174,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f194,plain,
    ( ~ spl2_5
    | ~ spl2_8
    | ~ spl2_11
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_11
    | spl2_20 ),
    inference(unit_resulting_resolution,[],[f109,f123,f139,f190,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f190,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f139,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_11
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f123,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f191,plain,
    ( ~ spl2_4
    | ~ spl2_20
    | spl2_19 ),
    inference(avatar_split_clause,[],[f186,f182,f188,f92])).

fof(f186,plain,
    ( sK0 != k2_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl2_19 ),
    inference(superposition,[],[f184,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f184,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f185,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_18
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f102,f92,f182,f131,f178,f82,f77])).

fof(f102,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v2_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f175,plain,
    ( ~ spl2_17
    | spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f170,f166,f112,f172])).

fof(f112,plain,
    ( spl2_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f170,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_6
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f114,f168])).

fof(f114,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f169,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_16
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f97,f92,f166,f87,f82,f77])).

fof(f87,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f97,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f152,plain,
    ( ~ spl2_4
    | spl2_13
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f146,f142,f149,f92])).

fof(f142,plain,
    ( spl2_12
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f146,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_12 ),
    inference(superposition,[],[f144,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

% (14912)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_12
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f96,f92,f142,f82,f77])).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f57])).

% (14926)Refutation not found, incomplete strategy% (14926)------------------------------
% (14926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14926)Termination reason: Refutation not found, incomplete strategy

% (14926)Memory used [KB]: 1791
% (14926)Time elapsed: 0.150 s
% (14926)------------------------------
% (14926)------------------------------
fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f140,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f101,f92,f87,f77,f137])).

fof(f101,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f134,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f100,f92,f87,f77,f131])).

fof(f100,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f124,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f99,f92,f121])).

fof(f99,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f71,f116,f112])).

fof(f71,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f49,f50,f50])).

fof(f49,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (14917)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

% (14935)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f110,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f98,f92,f107])).

fof(f98,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f46,f82])).

fof(f46,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f45,f77])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.30/0.54  % (14922)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.55  % (14914)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.55  % (14922)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.53/0.56  % (14918)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.57  % (14933)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f313,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f110,f119,f124,f134,f140,f145,f152,f169,f175,f185,f191,f194,f222,f225,f279,f281,f291,f309,f312])).
% 1.53/0.57  fof(f312,plain,(
% 1.53/0.57    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_32 | ~spl2_20 | spl2_36),
% 1.53/0.57    inference(avatar_split_clause,[],[f311,f306,f188,f276,f131,f77,f107])).
% 1.53/0.57  fof(f107,plain,(
% 1.53/0.57    spl2_5 <=> v1_relat_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.53/0.57  fof(f77,plain,(
% 1.53/0.57    spl2_1 <=> v1_funct_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.53/0.57  fof(f131,plain,(
% 1.53/0.57    spl2_10 <=> v2_funct_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.53/0.57  fof(f276,plain,(
% 1.53/0.57    spl2_32 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.53/0.57  fof(f188,plain,(
% 1.53/0.57    spl2_20 <=> sK0 = k2_relat_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.53/0.57  fof(f306,plain,(
% 1.53/0.57    spl2_36 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 1.53/0.57  fof(f311,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_20 | spl2_36)),
% 1.53/0.57    inference(forward_demodulation,[],[f310,f189])).
% 1.53/0.57  fof(f189,plain,(
% 1.53/0.57    sK0 = k2_relat_1(sK1) | ~spl2_20),
% 1.53/0.57    inference(avatar_component_clause,[],[f188])).
% 1.53/0.57  fof(f310,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_36),
% 1.53/0.57    inference(superposition,[],[f308,f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(flattening,[],[f21])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.53/0.57  fof(f308,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_36),
% 1.53/0.57    inference(avatar_component_clause,[],[f306])).
% 1.53/0.57  fof(f309,plain,(
% 1.53/0.57    ~spl2_18 | ~spl2_23 | ~spl2_1 | ~spl2_4 | ~spl2_36 | spl2_33),
% 1.53/0.57    inference(avatar_split_clause,[],[f292,f288,f306,f92,f77,f215,f178])).
% 1.53/0.57  fof(f178,plain,(
% 1.53/0.57    spl2_18 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.53/0.57  fof(f215,plain,(
% 1.53/0.57    spl2_23 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.53/0.57  fof(f92,plain,(
% 1.53/0.57    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.53/0.57  fof(f288,plain,(
% 1.53/0.57    spl2_33 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.53/0.57  fof(f292,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl2_33),
% 1.53/0.57    inference(superposition,[],[f290,f70])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f40])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.53/0.57    inference(flattening,[],[f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.53/0.57    inference(ennf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.53/0.57  fof(f290,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_33),
% 1.53/0.57    inference(avatar_component_clause,[],[f288])).
% 1.53/0.57  fof(f291,plain,(
% 1.53/0.57    ~spl2_33 | spl2_7 | ~spl2_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f282,f166,f116,f288])).
% 1.53/0.57  fof(f116,plain,(
% 1.53/0.57    spl2_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.53/0.57  fof(f166,plain,(
% 1.53/0.57    spl2_16 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.53/0.57  fof(f282,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl2_7 | ~spl2_16)),
% 1.53/0.57    inference(forward_demodulation,[],[f118,f168])).
% 1.53/0.57  fof(f168,plain,(
% 1.53/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_16),
% 1.53/0.57    inference(avatar_component_clause,[],[f166])).
% 1.53/0.57  fof(f118,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f116])).
% 1.53/0.57  fof(f281,plain,(
% 1.53/0.57    spl2_32),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f280])).
% 1.53/0.57  fof(f280,plain,(
% 1.53/0.57    $false | spl2_32),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f72,f278,f75])).
% 1.53/0.57  % (14926)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.53/0.57  fof(f75,plain,(
% 1.53/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f74])).
% 1.53/0.57  fof(f74,plain,(
% 1.53/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(equality_resolution,[],[f69])).
% 1.53/0.57  fof(f69,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(nnf_transformation,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(flattening,[],[f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.53/0.57  fof(f278,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl2_32),
% 1.53/0.57    inference(avatar_component_clause,[],[f276])).
% 1.53/0.57  fof(f72,plain,(
% 1.53/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f51,f50])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,axiom,(
% 1.53/0.57    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.53/0.57    inference(pure_predicate_removal,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.53/0.57  fof(f279,plain,(
% 1.53/0.57    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_32 | ~spl2_13 | spl2_24),
% 1.53/0.57    inference(avatar_split_clause,[],[f245,f219,f149,f276,f131,f77,f107])).
% 1.53/0.57  fof(f149,plain,(
% 1.53/0.57    spl2_13 <=> sK0 = k1_relat_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.53/0.57  fof(f219,plain,(
% 1.53/0.57    spl2_24 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.53/0.57  fof(f245,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_13 | spl2_24)),
% 1.53/0.57    inference(forward_demodulation,[],[f244,f151])).
% 1.53/0.57  fof(f151,plain,(
% 1.53/0.57    sK0 = k1_relat_1(sK1) | ~spl2_13),
% 1.53/0.57    inference(avatar_component_clause,[],[f149])).
% 1.53/0.57  fof(f244,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_24),
% 1.53/0.57    inference(superposition,[],[f221,f52])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f22])).
% 1.53/0.57  fof(f221,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_24),
% 1.53/0.57    inference(avatar_component_clause,[],[f219])).
% 1.53/0.57  fof(f225,plain,(
% 1.53/0.57    ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_10 | ~spl2_19 | spl2_23),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f223])).
% 1.53/0.57  fof(f223,plain,(
% 1.53/0.57    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_10 | ~spl2_19 | spl2_23)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f79,f133,f84,f94,f183,f217,f67])).
% 1.53/0.57  fof(f67,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.57    inference(flattening,[],[f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.53/0.57  fof(f217,plain,(
% 1.53/0.57    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_23),
% 1.53/0.57    inference(avatar_component_clause,[],[f215])).
% 1.53/0.57  fof(f183,plain,(
% 1.53/0.57    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl2_19),
% 1.53/0.57    inference(avatar_component_clause,[],[f182])).
% 1.53/0.57  fof(f182,plain,(
% 1.53/0.57    spl2_19 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.53/0.57  fof(f94,plain,(
% 1.53/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f92])).
% 1.53/0.57  fof(f84,plain,(
% 1.53/0.57    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f82])).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.53/0.57  fof(f133,plain,(
% 1.53/0.57    v2_funct_1(sK1) | ~spl2_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f131])).
% 1.53/0.57  fof(f79,plain,(
% 1.53/0.57    v1_funct_1(sK1) | ~spl2_1),
% 1.53/0.57    inference(avatar_component_clause,[],[f77])).
% 1.53/0.57  fof(f222,plain,(
% 1.53/0.57    ~spl2_1 | ~spl2_4 | ~spl2_18 | ~spl2_23 | ~spl2_24 | spl2_17),
% 1.53/0.57    inference(avatar_split_clause,[],[f176,f172,f219,f215,f178,f92,f77])).
% 1.53/0.57  fof(f172,plain,(
% 1.53/0.57    spl2_17 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.53/0.57  fof(f176,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl2_17),
% 1.53/0.57    inference(superposition,[],[f174,f70])).
% 1.53/0.57  fof(f174,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_17),
% 1.53/0.57    inference(avatar_component_clause,[],[f172])).
% 1.53/0.57  fof(f194,plain,(
% 1.53/0.57    ~spl2_5 | ~spl2_8 | ~spl2_11 | spl2_20),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f192])).
% 1.53/0.57  fof(f192,plain,(
% 1.53/0.57    $false | (~spl2_5 | ~spl2_8 | ~spl2_11 | spl2_20)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f109,f123,f139,f190,f54])).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(nnf_transformation,[],[f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(flattening,[],[f23])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.53/0.57  fof(f190,plain,(
% 1.53/0.57    sK0 != k2_relat_1(sK1) | spl2_20),
% 1.53/0.57    inference(avatar_component_clause,[],[f188])).
% 1.53/0.57  fof(f139,plain,(
% 1.53/0.57    v2_funct_2(sK1,sK0) | ~spl2_11),
% 1.53/0.57    inference(avatar_component_clause,[],[f137])).
% 1.53/0.57  fof(f137,plain,(
% 1.53/0.57    spl2_11 <=> v2_funct_2(sK1,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.53/0.57  fof(f123,plain,(
% 1.53/0.57    v5_relat_1(sK1,sK0) | ~spl2_8),
% 1.53/0.57    inference(avatar_component_clause,[],[f121])).
% 1.53/0.57  fof(f121,plain,(
% 1.53/0.57    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.53/0.57  fof(f109,plain,(
% 1.53/0.57    v1_relat_1(sK1) | ~spl2_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f107])).
% 1.53/0.57  fof(f191,plain,(
% 1.53/0.57    ~spl2_4 | ~spl2_20 | spl2_19),
% 1.53/0.57    inference(avatar_split_clause,[],[f186,f182,f188,f92])).
% 1.53/0.57  fof(f186,plain,(
% 1.53/0.57    sK0 != k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl2_19),
% 1.53/0.57    inference(superposition,[],[f184,f60])).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f31])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.53/0.57  fof(f184,plain,(
% 1.53/0.57    sK0 != k2_relset_1(sK0,sK0,sK1) | spl2_19),
% 1.53/0.57    inference(avatar_component_clause,[],[f182])).
% 1.53/0.57  fof(f185,plain,(
% 1.53/0.57    ~spl2_1 | ~spl2_2 | spl2_18 | ~spl2_10 | ~spl2_19 | ~spl2_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f102,f92,f182,f131,f178,f82,f77])).
% 1.53/0.57  fof(f102,plain,(
% 1.53/0.57    sK0 != k2_relset_1(sK0,sK0,sK1) | ~v2_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.57    inference(resolution,[],[f94,f65])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_1(k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f36])).
% 1.53/0.57  fof(f175,plain,(
% 1.53/0.57    ~spl2_17 | spl2_6 | ~spl2_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f170,f166,f112,f172])).
% 1.53/0.57  fof(f112,plain,(
% 1.53/0.57    spl2_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.53/0.57  fof(f170,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl2_6 | ~spl2_16)),
% 1.53/0.57    inference(backward_demodulation,[],[f114,f168])).
% 1.53/0.57  fof(f114,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f112])).
% 1.53/0.57  fof(f169,plain,(
% 1.53/0.57    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_16 | ~spl2_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f97,f92,f166,f87,f82,f77])).
% 1.53/0.57  fof(f87,plain,(
% 1.53/0.57    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.53/0.57  fof(f97,plain,(
% 1.53/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.57    inference(resolution,[],[f94,f56])).
% 1.53/0.57  fof(f56,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.57    inference(flattening,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.53/0.57  fof(f152,plain,(
% 1.53/0.57    ~spl2_4 | spl2_13 | ~spl2_12),
% 1.53/0.57    inference(avatar_split_clause,[],[f146,f142,f149,f92])).
% 1.53/0.57  fof(f142,plain,(
% 1.53/0.57    spl2_12 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.53/0.57  fof(f146,plain,(
% 1.53/0.57    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_12),
% 1.53/0.57    inference(superposition,[],[f144,f59])).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f30])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.53/0.57  % (14912)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.53/0.57  fof(f144,plain,(
% 1.53/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_12),
% 1.53/0.57    inference(avatar_component_clause,[],[f142])).
% 1.53/0.57  fof(f145,plain,(
% 1.53/0.57    ~spl2_1 | ~spl2_2 | spl2_12 | ~spl2_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f96,f92,f142,f82,f77])).
% 1.53/0.57  fof(f96,plain,(
% 1.53/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.57    inference(resolution,[],[f94,f57])).
% 1.53/0.57  % (14926)Refutation not found, incomplete strategy% (14926)------------------------------
% 1.53/0.57  % (14926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (14926)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (14926)Memory used [KB]: 1791
% 1.53/0.57  % (14926)Time elapsed: 0.150 s
% 1.53/0.57  % (14926)------------------------------
% 1.53/0.57  % (14926)------------------------------
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f28])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.57    inference(flattening,[],[f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,axiom,(
% 1.53/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f101,f92,f87,f77,f137])).
% 1.53/0.57  fof(f101,plain,(
% 1.53/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl2_4),
% 1.53/0.57    inference(resolution,[],[f94,f64])).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.53/0.58  fof(f134,plain,(
% 1.53/0.58    spl2_10 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f100,f92,f87,f77,f131])).
% 1.53/0.58  fof(f100,plain,(
% 1.53/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f94,f63])).
% 1.53/0.58  fof(f63,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f124,plain,(
% 1.53/0.58    spl2_8 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f99,f92,f121])).
% 1.53/0.58  fof(f99,plain,(
% 1.53/0.58    v5_relat_1(sK1,sK0) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f94,f61])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.53/0.58    inference(pure_predicate_removal,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.58  fof(f119,plain,(
% 1.53/0.58    ~spl2_6 | ~spl2_7),
% 1.53/0.58    inference(avatar_split_clause,[],[f71,f116,f112])).
% 1.53/0.58  fof(f71,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.53/0.58    inference(definition_unfolding,[],[f49,f50,f50])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f41])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  % (14917)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.53/0.58    inference(flattening,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f16])).
% 1.53/0.58  % (14935)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.58  fof(f16,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.53/0.58    inference(negated_conjecture,[],[f15])).
% 1.53/0.58  fof(f15,conjecture,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 1.53/0.58  fof(f110,plain,(
% 1.53/0.58    spl2_5 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f98,f92,f107])).
% 1.53/0.58  fof(f98,plain,(
% 1.53/0.58    v1_relat_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f94,f58])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.58  fof(f95,plain,(
% 1.53/0.58    spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f48,f92])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f90,plain,(
% 1.53/0.58    spl2_3),
% 1.53/0.58    inference(avatar_split_clause,[],[f47,f87])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    v3_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f85,plain,(
% 1.53/0.58    spl2_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f46,f82])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    v1_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    spl2_1),
% 1.53/0.58    inference(avatar_split_clause,[],[f45,f77])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    v1_funct_1(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (14922)------------------------------
% 1.53/0.58  % (14922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (14922)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (14922)Memory used [KB]: 11001
% 1.53/0.58  % (14922)Time elapsed: 0.138 s
% 1.53/0.58  % (14922)------------------------------
% 1.53/0.58  % (14922)------------------------------
% 1.53/0.58  % (14924)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.58  % (14923)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.58  % (14911)Success in time 0.22 s
%------------------------------------------------------------------------------
