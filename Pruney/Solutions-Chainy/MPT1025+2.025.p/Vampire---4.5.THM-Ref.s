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
% DateTime   : Thu Dec  3 13:06:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 314 expanded)
%              Number of leaves         :   31 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  545 ( 971 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f551,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f86,f90,f95,f102,f121,f131,f135,f144,f148,f159,f175,f192,f199,f329,f333,f338,f494,f550])).

fof(f550,plain,
    ( spl10_43
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f545,f197,f190,f129,f100,f93,f65,f454])).

fof(f454,plain,
    ( spl10_43
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f65,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f93,plain,
    ( spl10_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f100,plain,
    ( spl10_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f129,plain,
    ( spl10_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f190,plain,
    ( spl10_18
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f197,plain,
    ( spl10_19
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f545,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f544,f198])).

fof(f198,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f544,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18 ),
    inference(subsumption_resolution,[],[f540,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f540,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_18 ),
    inference(resolution,[],[f500,f94])).

fof(f94,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f500,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7
    | spl10_18 ),
    inference(subsumption_resolution,[],[f166,f191])).

fof(f191,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f166,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f165,f101])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f161,f66])).

fof(f66,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f161,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f44,f69])).

fof(f69,plain,
    ( ! [X3] : k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f494,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_43 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f492,f85])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f492,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_35
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f491,f435])).

fof(f435,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl10_34
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f433,f328])).

fof(f328,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl10_34
  <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f433,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl10_35 ),
    inference(resolution,[],[f332,f32])).

fof(f32,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f332,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl10_35
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f491,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f483,f62])).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f483,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_43 ),
    inference(resolution,[],[f455,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f455,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f454])).

fof(f338,plain,
    ( ~ spl10_18
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f230,f170,f190])).

fof(f170,plain,
    ( spl10_15
  <=> r2_hidden(sK8(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f230,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_15 ),
    inference(resolution,[],[f171,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f171,plain,
    ( r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f333,plain,
    ( spl10_35
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f316,f197,f190,f129,f100,f93,f65,f331])).

fof(f316,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f315,f198])).

fof(f315,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18 ),
    inference(subsumption_resolution,[],[f312,f130])).

fof(f312,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_18 ),
    inference(resolution,[],[f228,f94])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7
    | spl10_18 ),
    inference(subsumption_resolution,[],[f164,f191])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f163,f101])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f160,f66])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f43,f69])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK6(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f329,plain,
    ( spl10_34
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f305,f197,f190,f129,f100,f93,f65,f327])).

fof(f305,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f304,f198])).

fof(f304,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_18 ),
    inference(subsumption_resolution,[],[f301,f130])).

fof(f301,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_18 ),
    inference(resolution,[],[f226,f94])).

fof(f226,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7
    | spl10_18 ),
    inference(subsumption_resolution,[],[f168,f191])).

fof(f168,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f167,f101])).

fof(f167,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f162,f66])).

fof(f162,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f45,f69])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK6(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f199,plain,
    ( spl10_19
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f195,f93,f65,f197])).

fof(f195,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(resolution,[],[f109,f79])).

fof(f79,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK3,X4),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f70,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X4),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f94,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f192,plain,
    ( ~ spl10_18
    | spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f180,f173,f146,f190])).

fof(f146,plain,
    ( spl10_14
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f173,plain,
    ( spl10_16
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f180,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_14
    | ~ spl10_16 ),
    inference(superposition,[],[f147,f174])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f147,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f175,plain,
    ( spl10_15
    | spl10_16
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f80,f65,f173,f170])).

fof(f80,plain,
    ( sK0 = k1_relat_1(sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f72,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK8(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f159,plain,
    ( ~ spl10_6
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f152,f142,f97])).

fof(f97,plain,
    ( spl10_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f142,plain,
    ( spl10_13
  <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_13 ),
    inference(resolution,[],[f143,f42])).

% (17505)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f143,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f148,plain,
    ( ~ spl10_14
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f137,f133,f146])).

fof(f133,plain,
    ( spl10_12
  <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f137,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(resolution,[],[f134,f42])).

fof(f134,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f144,plain,
    ( spl10_13
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f111,f93,f84,f142])).

fof(f111,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f106,f85])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f135,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f110,f93,f84,f133])).

fof(f110,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f105,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f94,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,
    ( ~ spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f122,f119,f129])).

fof(f119,plain,
    ( spl10_9
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f112,f93,f84,f119])).

fof(f112,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f107,f85])).

fof(f107,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f94,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,
    ( spl10_6
    | ~ spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f71,f65,f100,f97])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f95,plain,
    ( spl10_5
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f91,f88,f65,f93])).

fof(f88,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f91,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f89,f69])).

fof(f89,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f76,f65,f84])).

fof(f76,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:08:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (17497)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.42  % (17497)Refutation not found, incomplete strategy% (17497)------------------------------
% 0.20/0.42  % (17497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (17497)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (17497)Memory used [KB]: 11001
% 0.20/0.42  % (17497)Time elapsed: 0.014 s
% 0.20/0.42  % (17497)------------------------------
% 0.20/0.42  % (17497)------------------------------
% 0.20/0.45  % (17501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (17500)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (17486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (17495)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (17492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (17496)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (17494)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (17491)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (17490)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (17488)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (17493)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (17502)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (17489)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (17506)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (17486)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f63,f67,f86,f90,f95,f102,f121,f131,f135,f144,f148,f159,f175,f192,f199,f329,f333,f338,f494,f550])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    spl10_43 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f545,f197,f190,f129,f100,f93,f65,f454])).
% 0.20/0.50  fof(f454,plain,(
% 0.20/0.50    spl10_43 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl10_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl10_7 <=> v1_xboole_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl10_11 <=> v1_xboole_0(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl10_18 <=> v1_xboole_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl10_19 <=> m1_subset_1(sK4,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.50  fof(f545,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f544,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    m1_subset_1(sK4,sK1) | ~spl10_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f197])).
% 0.20/0.50  fof(f544,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f540,f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2) | spl10_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f129])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(resolution,[],[f500,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f166,f191])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | spl10_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f165,f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | spl10_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f65])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f44,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X3] : (k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)) ) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.20/0.50  fof(f494,plain,(
% 0.20/0.50    ~spl10_1 | ~spl10_3 | ~spl10_34 | ~spl10_35 | ~spl10_43),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f493])).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    $false | (~spl10_1 | ~spl10_3 | ~spl10_34 | ~spl10_35 | ~spl10_43)),
% 0.20/0.50    inference(subsumption_resolution,[],[f492,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v1_relat_1(sK3) | ~spl10_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl10_3 <=> v1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_34 | ~spl10_35 | ~spl10_43)),
% 0.20/0.50    inference(subsumption_resolution,[],[f491,f435])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (~spl10_34 | ~spl10_35)),
% 0.20/0.50    inference(subsumption_resolution,[],[f433,f328])).
% 0.20/0.50  fof(f328,plain,(
% 0.20/0.50    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | ~spl10_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f327])).
% 0.20/0.50  fof(f327,plain,(
% 0.20/0.50    spl10_34 <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl10_35),
% 0.20/0.50    inference(resolution,[],[f332,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl10_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f331])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    spl10_35 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_43)),
% 0.20/0.50    inference(subsumption_resolution,[],[f483,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v1_funct_1(sK3) | ~spl10_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl10_1 <=> v1_funct_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.50  fof(f483,plain,(
% 0.20/0.50    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl10_43),
% 0.20/0.50    inference(resolution,[],[f455,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.50  fof(f455,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f454])).
% 0.20/0.50  fof(f338,plain,(
% 0.20/0.50    ~spl10_18 | ~spl10_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f230,f170,f190])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl10_15 <=> r2_hidden(sK8(sK0,sK3),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | ~spl10_15),
% 0.20/0.50    inference(resolution,[],[f171,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f170])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl10_35 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f316,f197,f190,f129,f100,f93,f65,f331])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f315,f198])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f312,f130])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(resolution,[],[f228,f94])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f164,f191])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f101])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f66])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f43,f69])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    spl10_34 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f305,f197,f190,f129,f100,f93,f65,f327])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18 | ~spl10_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f304,f198])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f301,f130])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(resolution,[],[f226,f94])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7 | spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f168,f191])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f167,f101])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f66])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f45,f69])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    spl10_19 | ~spl10_2 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f195,f93,f65,f197])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    m1_subset_1(sK4,sK1) | (~spl10_2 | ~spl10_5)),
% 0.20/0.50    inference(resolution,[],[f109,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X4] : (m1_subset_1(k9_relat_1(sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.20/0.50    inference(forward_demodulation,[],[f70,f69])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X4] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f94,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ~spl10_18 | spl10_14 | ~spl10_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f180,f173,f146,f190])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    spl10_14 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    spl10_16 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | (spl10_14 | ~spl10_16)),
% 0.20/0.50    inference(superposition,[],[f147,f174])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK3) | ~spl10_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f173])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_relat_1(sK3)) | spl10_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f146])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    spl10_15 | spl10_16 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f80,f65,f173,f170])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ~spl10_6 | ~spl10_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f152,f142,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl10_6 <=> v1_xboole_0(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl10_13 <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~v1_xboole_0(sK3) | ~spl10_13),
% 0.20/0.50    inference(resolution,[],[f143,f42])).
% 0.20/0.50  % (17505)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~spl10_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f142])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ~spl10_14 | ~spl10_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f137,f133,f146])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl10_12 <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl10_12),
% 0.20/0.50    inference(resolution,[],[f134,f42])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl10_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f133])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    spl10_13 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f111,f93,f84,f142])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f106,f85])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f94,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl10_12 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f110,f93,f84,f133])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f85])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f94,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ~spl10_11 | ~spl10_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f122,f119,f129])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl10_9 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2) | ~spl10_9),
% 0.20/0.50    inference(resolution,[],[f120,f42])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl10_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl10_9 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f112,f93,f84,f119])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f85])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f94,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl10_6 | ~spl10_7 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f71,f65,f100,f97])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl10_5 | ~spl10_2 | ~spl10_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f91,f88,f65,f93])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_2 | ~spl10_4)),
% 0.20/0.50    inference(forward_demodulation,[],[f89,f69])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f88])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl10_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f88])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl10_3 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f76,f65,f84])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v1_relat_1(sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f66,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f65])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl10_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f61])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (17486)------------------------------
% 0.20/0.50  % (17486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17486)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (17486)Memory used [KB]: 6524
% 0.20/0.50  % (17486)Time elapsed: 0.080 s
% 0.20/0.50  % (17486)------------------------------
% 0.20/0.50  % (17486)------------------------------
% 0.20/0.50  % (17487)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (17504)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (17487)Refutation not found, incomplete strategy% (17487)------------------------------
% 0.20/0.50  % (17487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17487)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17487)Memory used [KB]: 10618
% 0.20/0.50  % (17487)Time elapsed: 0.093 s
% 0.20/0.50  % (17487)------------------------------
% 0.20/0.50  % (17487)------------------------------
% 0.20/0.51  % (17498)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17485)Success in time 0.162 s
%------------------------------------------------------------------------------
