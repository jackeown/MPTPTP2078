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
% DateTime   : Thu Dec  3 12:57:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 202 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  330 ( 594 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f67,f79,f83,f90,f94,f107,f114,f135,f141,f152,f156,f185,f194,f200,f211,f246])).

fof(f246,plain,
    ( ~ spl10_14
    | ~ spl10_19
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl10_14
    | ~ spl10_19
    | spl10_21 ),
    inference(subsumption_resolution,[],[f244,f210])).

fof(f210,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl10_21
  <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f244,plain,
    ( m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_14
    | ~ spl10_19 ),
    inference(resolution,[],[f196,f151])).

fof(f151,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_14
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK4,sK1,sK3),X0) )
    | ~ spl10_19 ),
    inference(resolution,[],[f193,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f193,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl10_19
  <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f211,plain,
    ( ~ spl10_21
    | ~ spl10_13
    | ~ spl10_17
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f205,f198,f183,f133,f209])).

fof(f133,plain,
    ( spl10_13
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f183,plain,
    ( spl10_17
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f198,plain,
    ( spl10_20
  <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f205,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_13
    | ~ spl10_17
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f201,f184])).

fof(f184,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f201,plain,
    ( ~ r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_13
    | ~ spl10_20 ),
    inference(resolution,[],[f199,f134])).

fof(f134,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f199,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl10_20
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f164,f88,f65,f198])).

fof(f65,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f88,plain,
    ( spl10_8
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f164,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f160,f66])).

fof(f66,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f160,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f89,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f194,plain,
    ( spl10_19
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f163,f88,f65,f192])).

fof(f163,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f159,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f89,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f185,plain,
    ( spl10_17
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f165,f88,f65,f183])).

fof(f165,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f161,f66])).

fof(f161,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,
    ( spl10_10
    | ~ spl10_7
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f155,f112,f81,f105])).

fof(f105,plain,
    ( spl10_10
  <=> sP8(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f81,plain,
    ( spl10_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f112,plain,
    ( spl10_11
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f155,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_7
    | ~ spl10_11 ),
    inference(resolution,[],[f142,f82])).

fof(f82,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP8(sK4,X0,sK3) )
    | ~ spl10_11 ),
    inference(resolution,[],[f113,f33])).

fof(f33,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

% (15519)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f113,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f152,plain,
    ( spl10_14
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f110,f92,f150])).

fof(f92,plain,
    ( spl10_9
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f110,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_9 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f141,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f139,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | spl10_4 ),
    inference(forward_demodulation,[],[f131,f60])).

fof(f60,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f57,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f131,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f139,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f118,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_10 ),
    inference(resolution,[],[f106,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f135,plain,
    ( ~ spl10_4
    | spl10_13 ),
    inference(avatar_split_clause,[],[f23,f133,f69])).

fof(f23,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f114,plain,
    ( spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f25,f112,f69])).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f107,plain,
    ( spl10_10
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f100,f88,f65,f105])).

fof(f100,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f95,f66])).

fof(f95,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP8(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f86,f77,f65,f92])).

fof(f77,plain,
    ( spl10_6
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f86,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl10_3
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f85,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f78,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f78,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f90,plain,
    ( spl10_8
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f84,f69,f56,f88])).

fof(f84,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f70,f60])).

fof(f70,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f83,plain,
    ( spl10_4
    | spl10_7 ),
    inference(avatar_split_clause,[],[f26,f81,f69])).

fof(f26,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( spl10_6
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f59,f56,f77])).

fof(f59,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f67,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f63,f56,f65])).

fof(f63,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f62,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f58,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15535)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (15527)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (15518)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (15518)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (15537)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f58,f67,f79,f83,f90,f94,f107,f114,f135,f141,f152,f156,f185,f194,f200,f211,f246])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    ~spl10_14 | ~spl10_19 | spl10_21),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f245])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    $false | (~spl10_14 | ~spl10_19 | spl10_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f244,f210])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | spl10_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f209])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    spl10_21 <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_14 | ~spl10_19)),
% 0.21/0.47    inference(resolution,[],[f196,f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl10_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    spl10_14 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK4,sK1,sK3),X0)) ) | ~spl10_19),
% 0.21/0.47    inference(resolution,[],[f193,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~spl10_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    spl10_19 <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ~spl10_21 | ~spl10_13 | ~spl10_17 | ~spl10_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f205,f198,f183,f133,f209])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl10_13 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    spl10_17 <=> r2_hidden(sK6(sK4,sK1,sK3),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl10_20 <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_13 | ~spl10_17 | ~spl10_20)),
% 0.21/0.47    inference(subsumption_resolution,[],[f201,f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~spl10_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f183])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    ~r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_13 | ~spl10_20)),
% 0.21/0.47    inference(resolution,[],[f199,f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~spl10_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f198])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    spl10_20 | ~spl10_3 | ~spl10_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f164,f88,f65,f198])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl10_3 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl10_8 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | (~spl10_3 | ~spl10_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f160,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl10_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.47    inference(resolution,[],[f89,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    spl10_19 | ~spl10_3 | ~spl10_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f163,f88,f65,f192])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | (~spl10_3 | ~spl10_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f159,f66])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.47    inference(resolution,[],[f89,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    spl10_17 | ~spl10_3 | ~spl10_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f165,f88,f65,f183])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),sK1) | (~spl10_3 | ~spl10_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f161,f66])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.47    inference(resolution,[],[f89,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    spl10_10 | ~spl10_7 | ~spl10_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f155,f112,f81,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl10_10 <=> sP8(sK4,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl10_7 <=> r2_hidden(sK5,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl10_11 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    sP8(sK4,sK1,sK3) | (~spl10_7 | ~spl10_11)),
% 0.21/0.47    inference(resolution,[],[f142,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    r2_hidden(sK5,sK1) | ~spl10_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK5,X0) | sP8(sK4,X0,sK3)) ) | ~spl10_11),
% 0.21/0.47    inference(resolution,[],[f113,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP8(X3,X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.47  % (15519)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl10_14 | ~spl10_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f92,f150])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl10_9 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl10_9),
% 0.21/0.47    inference(resolution,[],[f93,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK3),sK2) | ~spl10_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    $false | (~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_10)),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | spl10_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f131,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl10_2),
% 0.21/0.47    inference(resolution,[],[f57,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl10_4 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_3 | ~spl10_10)),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f66])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_10),
% 0.21/0.47    inference(resolution,[],[f106,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    sP8(sK4,sK1,sK3) | ~spl10_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f105])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~spl10_4 | spl10_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f133,f69])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl10_4 | spl10_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f112,f69])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl10_10 | ~spl10_3 | ~spl10_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f100,f88,f65,f105])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    sP8(sK4,sK1,sK3) | (~spl10_3 | ~spl10_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f95,f66])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    sP8(sK4,sK1,sK3) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.21/0.47    inference(resolution,[],[f89,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP8(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl10_9 | ~spl10_3 | ~spl10_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f77,f65,f92])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl10_6 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK3),sK2) | (~spl10_3 | ~spl10_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f66])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~spl10_6),
% 0.21/0.47    inference(resolution,[],[f78,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v5_relat_1(sK3,sK2) | ~spl10_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl10_8 | ~spl10_2 | ~spl10_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f69,f56,f88])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | ~spl10_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f70,f60])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl10_4 | spl10_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f81,f69])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl10_6 | ~spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f56,f77])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    v5_relat_1(sK3,sK2) | ~spl10_2),
% 0.21/0.47    inference(resolution,[],[f57,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl10_3 | ~spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f63,f56,f65])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.47    inference(resolution,[],[f57,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (15518)------------------------------
% 0.21/0.47  % (15518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15518)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (15518)Memory used [KB]: 6268
% 0.21/0.47  % (15518)Time elapsed: 0.070 s
% 0.21/0.47  % (15518)------------------------------
% 0.21/0.47  % (15518)------------------------------
% 0.21/0.48  % (15517)Success in time 0.121 s
%------------------------------------------------------------------------------
