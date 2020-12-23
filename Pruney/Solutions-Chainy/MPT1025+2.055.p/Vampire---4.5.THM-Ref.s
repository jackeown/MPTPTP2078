%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 163 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 ( 475 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f60,f64,f69,f84,f94,f99,f116,f125,f129,f143,f150])).

fof(f150,plain,
    ( ~ spl6_16
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl6_16
    | spl6_17 ),
    inference(subsumption_resolution,[],[f148,f142])).

fof(f142,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_17
  <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f148,plain,
    ( m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f128,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f128,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_16
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f143,plain,
    ( ~ spl6_17
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f139,f123,f82,f58,f44,f141])).

fof(f44,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f58,plain,
    ( spl6_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f82,plain,
    ( spl6_7
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f123,plain,
    ( spl6_15
  <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f139,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f85,f138])).

fof(f138,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f137,f59])).

fof(f59,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f137,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f132,f45])).

fof(f45,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f132,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f124,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f124,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f85,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_7 ),
    inference(resolution,[],[f83,f24])).

fof(f24,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f83,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f129,plain,
    ( spl6_16
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f121,f114,f97,f127])).

fof(f97,plain,
    ( spl6_10
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f114,plain,
    ( spl6_14
  <=> r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f121,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(resolution,[],[f101,f115])).

fof(f115,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(X0,sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f98,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f125,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f75,f67,f58,f123])).

fof(f67,plain,
    ( spl6_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f71,f59])).

fof(f71,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f68,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f116,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f74,f67,f58,f114])).

fof(f74,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f70,f59])).

fof(f70,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f95,f92,f48,f97])).

fof(f48,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f92,plain,
    ( spl6_9
  <=> m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f95,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f93,f52])).

fof(f52,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f93,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl6_9
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f51,f48,f92])).

fof(f51,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f84,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f76,f67,f58,f82])).

fof(f76,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f72,f59])).

fof(f72,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( spl6_5
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f65,f62,f48,f67])).

fof(f62,plain,
    ( spl6_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f65,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f63,f53])).

fof(f53,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f63,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f56,f48,f58])).

fof(f56,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f54,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (32223)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.46  % (32220)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.46  % (32231)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.47  % (32218)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (32213)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (32226)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (32213)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f46,f50,f60,f64,f69,f84,f94,f99,f116,f125,f129,f143,f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~spl6_16 | spl6_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    $false | (~spl6_16 | spl6_17)),
% 0.22/0.48    inference(subsumption_resolution,[],[f148,f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | spl6_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl6_17 <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    m1_subset_1(sK5(sK4,sK2,sK3),sK0) | ~spl6_16),
% 0.22/0.48    inference(resolution,[],[f128,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~spl6_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl6_16 <=> r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ~spl6_17 | ~spl6_1 | ~spl6_3 | ~spl6_7 | ~spl6_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f139,f123,f82,f58,f44,f141])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl6_3 <=> v1_relat_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl6_7 <=> r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    spl6_15 <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | (~spl6_1 | ~spl6_3 | ~spl6_7 | ~spl6_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f85,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | (~spl6_1 | ~spl6_3 | ~spl6_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f137,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    v1_relat_1(sK3) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f44])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl6_15),
% 0.22/0.48    inference(resolution,[],[f124,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~spl6_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f123])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~spl6_7),
% 0.22/0.48    inference(resolution,[],[f83,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X5] : (~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~spl6_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f82])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl6_16 | ~spl6_10 | ~spl6_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f121,f114,f97,f127])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl6_10 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl6_14 <=> r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_10 | ~spl6_14)),
% 0.22/0.48    inference(resolution,[],[f101,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl6_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X0,sK0)) ) | ~spl6_10),
% 0.22/0.48    inference(resolution,[],[f98,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl6_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f97])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl6_15 | ~spl6_3 | ~spl6_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f75,f67,f58,f123])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl6_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | (~spl6_3 | ~spl6_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f71,f59])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl6_5),
% 0.22/0.48    inference(resolution,[],[f68,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl6_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl6_14 | ~spl6_3 | ~spl6_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f74,f67,f58,f114])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl6_3 | ~spl6_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f70,f59])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl6_5),
% 0.22/0.48    inference(resolution,[],[f68,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl6_10 | ~spl6_2 | ~spl6_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f95,f92,f48,f97])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl6_9 <=> m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | (~spl6_2 | ~spl6_9)),
% 0.22/0.48    inference(forward_demodulation,[],[f93,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f49,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) | ~spl6_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f92])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl6_9 | ~spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f51,f48,f92])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f49,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl6_7 | ~spl6_3 | ~spl6_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f76,f67,f58,f82])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK2) | (~spl6_3 | ~spl6_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f59])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl6_5),
% 0.22/0.48    inference(resolution,[],[f68,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl6_5 | ~spl6_2 | ~spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f65,f62,f48,f67])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl6_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_2 | ~spl6_4)),
% 0.22/0.48    inference(forward_demodulation,[],[f63,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f49,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f62])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl6_3 | ~spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f56,f48,f58])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    v1_relat_1(sK3) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f54,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f49,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f48])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f44])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v1_funct_1(sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (32213)------------------------------
% 0.22/0.48  % (32213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32213)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (32213)Memory used [KB]: 6140
% 0.22/0.48  % (32213)Time elapsed: 0.065 s
% 0.22/0.48  % (32213)------------------------------
% 0.22/0.48  % (32213)------------------------------
% 0.22/0.49  % (32212)Success in time 0.127 s
%------------------------------------------------------------------------------
