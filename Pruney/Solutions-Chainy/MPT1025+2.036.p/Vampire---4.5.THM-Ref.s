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
% DateTime   : Thu Dec  3 13:06:26 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 303 expanded)
%              Number of leaves         :   32 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  541 ( 947 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f85,f89,f94,f106,f119,f129,f133,f140,f154,f181,f191,f204,f358,f400,f416,f435,f442])).

fof(f442,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f440,f438])).

fof(f438,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f411,f437])).

fof(f437,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f431,f84])).

fof(f84,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f431,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f424,f60])).

fof(f60,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f424,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_38 ),
    inference(resolution,[],[f415,f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f415,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl10_38
  <=> r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f411,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl10_37 ),
    inference(resolution,[],[f399,f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f399,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl10_37
  <=> m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f440,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f439,f203])).

fof(f203,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl10_22
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f439,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f389,f128])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f389,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_14
    | spl10_19 ),
    inference(resolution,[],[f364,f93])).

fof(f93,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl10_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f364,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK5(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f348,f139])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl10_14
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f348,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK5(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2
    | spl10_19 ),
    inference(subsumption_resolution,[],[f173,f190])).

fof(f190,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl10_19
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f173,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK5(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f168,f64])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f168,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK5(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f42,f66])).

fof(f66,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f435,plain,
    ( sK0 != k1_relat_1(sK3)
    | v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f416,plain,
    ( spl10_38
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f406,f202,f189,f138,f127,f92,f63,f414])).

fof(f406,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f405,f203])).

fof(f405,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f401,f128])).

fof(f401,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_14
    | spl10_19 ),
    inference(resolution,[],[f363,f93])).

fof(f363,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f349,f139])).

fof(f349,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2
    | spl10_19 ),
    inference(subsumption_resolution,[],[f171,f190])).

fof(f171,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f167,f64])).

fof(f167,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f41,f66])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f400,plain,
    ( spl10_37
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f382,f202,f189,f138,f127,f92,f63,f398])).

fof(f382,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f381,f203])).

fof(f381,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_11
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f377,f128])).

fof(f377,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_14
    | spl10_19 ),
    inference(resolution,[],[f362,f93])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_14
    | spl10_19 ),
    inference(subsumption_resolution,[],[f350,f139])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2
    | spl10_19 ),
    inference(subsumption_resolution,[],[f169,f190])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f166,f64])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f40,f66])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f358,plain,
    ( spl10_6
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f105,f136])).

fof(f136,plain,
    ( ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl10_13
  <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f105,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK2))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl10_6
  <=> v1_xboole_0(k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f204,plain,
    ( spl10_22
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f192,f92,f63,f202])).

fof(f192,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(resolution,[],[f99,f75])).

fof(f75,plain,
    ( ! [X1] : m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f67,f66])).

fof(f67,plain,
    ( ! [X1] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X1),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f191,plain,
    ( ~ spl10_19
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f182,f176,f189])).

fof(f176,plain,
    ( spl10_17
  <=> r2_hidden(sK7(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f182,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_17 ),
    inference(resolution,[],[f177,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f177,plain,
    ( r2_hidden(sK7(sK0,sK3),sK0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f181,plain,
    ( spl10_17
    | spl10_18
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f78,f63,f179,f176])).

fof(f179,plain,
    ( spl10_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f78,plain,
    ( sK0 = k1_relat_1(sK3)
    | r2_hidden(sK7(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK7(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK7(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f154,plain,
    ( ~ spl10_16
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f143,f131,f152])).

fof(f152,plain,
    ( spl10_16
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f131,plain,
    ( spl10_12
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f143,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(resolution,[],[f132,f55])).

fof(f132,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f140,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f114,f63,f138,f135])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK1)
        | v1_xboole_0(k9_relat_1(sK3,X0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f133,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f100,f92,f83,f131])).

fof(f100,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f95,f84])).

fof(f95,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f129,plain,
    ( ~ spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f120,f117,f127])).

fof(f117,plain,
    ( spl10_9
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f120,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f118,f55])).

fof(f118,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f102,f92,f83,f117])).

fof(f102,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f97,f84])).

fof(f97,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,
    ( ~ spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f98,f92,f104])).

fof(f98,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f55])).

fof(f94,plain,
    ( spl10_5
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f90,f87,f63,f92])).

fof(f87,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f90,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f88,f66])).

fof(f88,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f31,f87])).

fof(f31,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f81,f63,f83])).

fof(f81,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:24:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (19115)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (19121)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (19112)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (19113)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (19120)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (19107)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19107)Refutation not found, incomplete strategy% (19107)------------------------------
% 0.21/0.51  % (19107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19107)Memory used [KB]: 10618
% 0.21/0.51  % (19107)Time elapsed: 0.076 s
% 0.21/0.51  % (19107)------------------------------
% 0.21/0.51  % (19107)------------------------------
% 0.21/0.53  % (19110)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (19111)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (19116)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.55  % (19106)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (19109)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (19122)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.56  % (19126)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.56  % (19124)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.56  % (19125)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.56  % (19126)Refutation not found, incomplete strategy% (19126)------------------------------
% 0.21/0.56  % (19126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19126)Memory used [KB]: 10618
% 0.21/0.56  % (19126)Time elapsed: 0.130 s
% 0.21/0.56  % (19126)------------------------------
% 0.21/0.56  % (19126)------------------------------
% 0.21/0.56  % (19119)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.63/0.57  % (19114)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.63/0.57  % (19118)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.57  % (19108)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.63/0.58  % (19117)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.63/0.58  % (19106)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f444,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f61,f65,f85,f89,f94,f106,f119,f129,f133,f140,f154,f181,f191,f204,f358,f400,f416,f435,f442])).
% 1.63/0.58  fof(f442,plain,(
% 1.63/0.58    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22 | ~spl10_37 | ~spl10_38),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f441])).
% 1.63/0.58  fof(f441,plain,(
% 1.63/0.58    $false | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22 | ~spl10_37 | ~spl10_38)),
% 1.63/0.58    inference(subsumption_resolution,[],[f440,f438])).
% 1.63/0.58  fof(f438,plain,(
% 1.63/0.58    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | (~spl10_1 | ~spl10_3 | ~spl10_37 | ~spl10_38)),
% 1.63/0.58    inference(subsumption_resolution,[],[f411,f437])).
% 1.63/0.58  fof(f437,plain,(
% 1.63/0.58    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | (~spl10_1 | ~spl10_3 | ~spl10_38)),
% 1.63/0.58    inference(subsumption_resolution,[],[f431,f84])).
% 1.63/0.58  fof(f84,plain,(
% 1.63/0.58    v1_relat_1(sK3) | ~spl10_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f83])).
% 1.63/0.58  fof(f83,plain,(
% 1.63/0.58    spl10_3 <=> v1_relat_1(sK3)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.63/0.58  fof(f431,plain,(
% 1.63/0.58    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_38)),
% 1.63/0.58    inference(subsumption_resolution,[],[f424,f60])).
% 1.63/0.58  fof(f60,plain,(
% 1.63/0.58    v1_funct_1(sK3) | ~spl10_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f59])).
% 1.63/0.58  fof(f59,plain,(
% 1.63/0.58    spl10_1 <=> v1_funct_1(sK3)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.63/0.58  fof(f424,plain,(
% 1.63/0.58    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl10_38),
% 1.63/0.58    inference(resolution,[],[f415,f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.63/0.58    inference(flattening,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.63/0.58    inference(ennf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.63/0.58  fof(f415,plain,(
% 1.63/0.58    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_38),
% 1.63/0.58    inference(avatar_component_clause,[],[f414])).
% 1.63/0.58  fof(f414,plain,(
% 1.63/0.58    spl10_38 <=> r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 1.63/0.58  fof(f411,plain,(
% 1.63/0.58    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~spl10_37),
% 1.63/0.58    inference(resolution,[],[f399,f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.63/0.58    inference(flattening,[],[f16])).
% 1.63/0.58  fof(f16,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.63/0.58    inference(ennf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.63/0.58    inference(pure_predicate_removal,[],[f14])).
% 1.63/0.58  fof(f14,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.63/0.58    inference(negated_conjecture,[],[f13])).
% 1.63/0.58  fof(f13,conjecture,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 1.63/0.58  fof(f399,plain,(
% 1.63/0.58    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl10_37),
% 1.63/0.58    inference(avatar_component_clause,[],[f398])).
% 1.63/0.58  fof(f398,plain,(
% 1.63/0.58    spl10_37 <=> m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 1.63/0.58  fof(f440,plain,(
% 1.63/0.58    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22)),
% 1.63/0.58    inference(subsumption_resolution,[],[f439,f203])).
% 1.63/0.58  fof(f203,plain,(
% 1.63/0.58    m1_subset_1(sK4,sK1) | ~spl10_22),
% 1.63/0.58    inference(avatar_component_clause,[],[f202])).
% 1.63/0.58  fof(f202,plain,(
% 1.63/0.58    spl10_22 <=> m1_subset_1(sK4,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.63/0.58  fof(f439,plain,(
% 1.63/0.58    ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f389,f128])).
% 1.63/0.58  fof(f128,plain,(
% 1.63/0.58    ~v1_xboole_0(sK2) | spl10_11),
% 1.63/0.58    inference(avatar_component_clause,[],[f127])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    spl10_11 <=> v1_xboole_0(sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.63/0.58  fof(f389,plain,(
% 1.63/0.58    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(resolution,[],[f364,f93])).
% 1.63/0.58  fof(f93,plain,(
% 1.63/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_5),
% 1.63/0.58    inference(avatar_component_clause,[],[f92])).
% 1.63/0.58  fof(f92,plain,(
% 1.63/0.58    spl10_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.63/0.58  fof(f364,plain,(
% 1.63/0.58    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(sK5(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f348,f139])).
% 1.63/0.58  fof(f139,plain,(
% 1.63/0.58    ~v1_xboole_0(sK1) | spl10_14),
% 1.63/0.58    inference(avatar_component_clause,[],[f138])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    spl10_14 <=> v1_xboole_0(sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.63/0.58  fof(f348,plain,(
% 1.63/0.58    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(sK5(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | (~spl10_2 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f173,f190])).
% 1.63/0.58  fof(f190,plain,(
% 1.63/0.58    ~v1_xboole_0(sK0) | spl10_19),
% 1.63/0.58    inference(avatar_component_clause,[],[f189])).
% 1.63/0.58  fof(f189,plain,(
% 1.63/0.58    spl10_19 <=> v1_xboole_0(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.63/0.58  fof(f173,plain,(
% 1.63/0.58    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK5(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(subsumption_resolution,[],[f168,f64])).
% 1.63/0.58  fof(f64,plain,(
% 1.63/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f63])).
% 1.63/0.58  fof(f63,plain,(
% 1.63/0.58    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.63/0.58  fof(f168,plain,(
% 1.63/0.58    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | r2_hidden(sK5(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(superposition,[],[f42,f66])).
% 1.63/0.58  fof(f66,plain,(
% 1.63/0.58    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f64,f38])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK5(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,axiom,(
% 1.63/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 1.63/0.58  fof(f435,plain,(
% 1.63/0.58    sK0 != k1_relat_1(sK3) | v1_xboole_0(k1_relat_1(sK3)) | ~v1_xboole_0(sK0)),
% 1.63/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.58  fof(f416,plain,(
% 1.63/0.58    spl10_38 | ~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22),
% 1.63/0.58    inference(avatar_split_clause,[],[f406,f202,f189,f138,f127,f92,f63,f414])).
% 1.63/0.58  fof(f406,plain,(
% 1.63/0.58    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22)),
% 1.63/0.58    inference(subsumption_resolution,[],[f405,f203])).
% 1.63/0.58  fof(f405,plain,(
% 1.63/0.58    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f401,f128])).
% 1.63/0.58  fof(f401,plain,(
% 1.63/0.58    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(resolution,[],[f363,f93])).
% 1.63/0.58  fof(f363,plain,(
% 1.63/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f349,f139])).
% 1.63/0.58  fof(f349,plain,(
% 1.63/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | (~spl10_2 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f171,f190])).
% 1.63/0.58  fof(f171,plain,(
% 1.63/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(subsumption_resolution,[],[f167,f64])).
% 1.63/0.58  fof(f167,plain,(
% 1.63/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK5(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(superposition,[],[f41,f66])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f400,plain,(
% 1.63/0.58    spl10_37 | ~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22),
% 1.63/0.58    inference(avatar_split_clause,[],[f382,f202,f189,f138,f127,f92,f63,f398])).
% 1.63/0.58  fof(f382,plain,(
% 1.63/0.58    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19 | ~spl10_22)),
% 1.63/0.58    inference(subsumption_resolution,[],[f381,f203])).
% 1.63/0.58  fof(f381,plain,(
% 1.63/0.58    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_11 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f377,f128])).
% 1.63/0.58  fof(f377,plain,(
% 1.63/0.58    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(resolution,[],[f362,f93])).
% 1.63/0.58  fof(f362,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_14 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f350,f139])).
% 1.63/0.58  fof(f350,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | (~spl10_2 | spl10_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f169,f190])).
% 1.63/0.58  fof(f169,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(subsumption_resolution,[],[f166,f64])).
% 1.63/0.58  fof(f166,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 1.63/0.58    inference(superposition,[],[f40,f66])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f358,plain,(
% 1.63/0.58    spl10_6 | ~spl10_13),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f355])).
% 1.63/0.58  fof(f355,plain,(
% 1.63/0.58    $false | (spl10_6 | ~spl10_13)),
% 1.63/0.58    inference(subsumption_resolution,[],[f105,f136])).
% 1.63/0.58  fof(f136,plain,(
% 1.63/0.58    ( ! [X0] : (v1_xboole_0(k9_relat_1(sK3,X0))) ) | ~spl10_13),
% 1.63/0.58    inference(avatar_component_clause,[],[f135])).
% 1.63/0.58  fof(f135,plain,(
% 1.63/0.58    spl10_13 <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.63/0.58  fof(f105,plain,(
% 1.63/0.58    ~v1_xboole_0(k9_relat_1(sK3,sK2)) | spl10_6),
% 1.63/0.58    inference(avatar_component_clause,[],[f104])).
% 1.63/0.58  fof(f104,plain,(
% 1.63/0.58    spl10_6 <=> v1_xboole_0(k9_relat_1(sK3,sK2))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.63/0.58  fof(f204,plain,(
% 1.63/0.58    spl10_22 | ~spl10_2 | ~spl10_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f192,f92,f63,f202])).
% 1.63/0.58  fof(f192,plain,(
% 1.63/0.58    m1_subset_1(sK4,sK1) | (~spl10_2 | ~spl10_5)),
% 1.63/0.58    inference(resolution,[],[f99,f75])).
% 1.63/0.58  fof(f75,plain,(
% 1.63/0.58    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 1.63/0.58    inference(forward_demodulation,[],[f67,f66])).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ( ! [X1] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X1),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f64,f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.63/0.58  fof(f99,plain,(
% 1.63/0.58    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl10_5),
% 1.63/0.58    inference(resolution,[],[f93,f37])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.63/0.58    inference(flattening,[],[f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.63/0.58  fof(f191,plain,(
% 1.63/0.58    ~spl10_19 | ~spl10_17),
% 1.63/0.58    inference(avatar_split_clause,[],[f182,f176,f189])).
% 1.63/0.58  fof(f176,plain,(
% 1.63/0.58    spl10_17 <=> r2_hidden(sK7(sK0,sK3),sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.63/0.58  fof(f182,plain,(
% 1.63/0.58    ~v1_xboole_0(sK0) | ~spl10_17),
% 1.63/0.58    inference(resolution,[],[f177,f55])).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    r2_hidden(sK7(sK0,sK3),sK0) | ~spl10_17),
% 1.63/0.58    inference(avatar_component_clause,[],[f176])).
% 1.63/0.58  fof(f181,plain,(
% 1.63/0.58    spl10_17 | spl10_18 | ~spl10_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f78,f63,f179,f176])).
% 1.63/0.58  fof(f179,plain,(
% 1.63/0.58    spl10_18 <=> sK0 = k1_relat_1(sK3)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.63/0.58  fof(f78,plain,(
% 1.63/0.58    sK0 = k1_relat_1(sK3) | r2_hidden(sK7(sK0,sK3),sK0) | ~spl10_2),
% 1.63/0.58    inference(forward_demodulation,[],[f70,f69])).
% 1.63/0.58  fof(f69,plain,(
% 1.63/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f64,f45])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK7(sK0,sK3),sK0) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f64,f50])).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK7(X1,X2),X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.63/0.58    inference(ennf_transformation,[],[f11])).
% 1.63/0.58  fof(f11,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.63/0.58  fof(f154,plain,(
% 1.63/0.58    ~spl10_16 | ~spl10_12),
% 1.63/0.58    inference(avatar_split_clause,[],[f143,f131,f152])).
% 1.63/0.58  fof(f152,plain,(
% 1.63/0.58    spl10_16 <=> v1_xboole_0(k1_relat_1(sK3))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.63/0.58  fof(f131,plain,(
% 1.63/0.58    spl10_12 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.63/0.58  fof(f143,plain,(
% 1.63/0.58    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl10_12),
% 1.63/0.58    inference(resolution,[],[f132,f55])).
% 1.63/0.58  fof(f132,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl10_12),
% 1.63/0.58    inference(avatar_component_clause,[],[f131])).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    spl10_13 | ~spl10_14 | ~spl10_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f114,f63,f138,f135])).
% 1.63/0.58  fof(f114,plain,(
% 1.63/0.58    ( ! [X0] : (~v1_xboole_0(sK1) | v1_xboole_0(k9_relat_1(sK3,X0))) ) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f75,f56])).
% 1.63/0.58  fof(f56,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f29])).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.63/0.58  fof(f133,plain,(
% 1.63/0.58    spl10_12 | ~spl10_3 | ~spl10_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f100,f92,f83,f131])).
% 1.63/0.58  fof(f100,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl10_3 | ~spl10_5)),
% 1.63/0.58    inference(subsumption_resolution,[],[f95,f84])).
% 1.63/0.58  fof(f95,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_5),
% 1.63/0.58    inference(resolution,[],[f93,f46])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.63/0.58    inference(ennf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.63/0.58  fof(f129,plain,(
% 1.63/0.58    ~spl10_11 | ~spl10_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f120,f117,f127])).
% 1.63/0.58  fof(f117,plain,(
% 1.63/0.58    spl10_9 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.63/0.58  fof(f120,plain,(
% 1.63/0.58    ~v1_xboole_0(sK2) | ~spl10_9),
% 1.63/0.58    inference(resolution,[],[f118,f55])).
% 1.63/0.58  fof(f118,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl10_9),
% 1.63/0.58    inference(avatar_component_clause,[],[f117])).
% 1.63/0.58  fof(f119,plain,(
% 1.63/0.58    spl10_9 | ~spl10_3 | ~spl10_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f102,f92,f83,f117])).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl10_3 | ~spl10_5)),
% 1.63/0.58    inference(subsumption_resolution,[],[f97,f84])).
% 1.63/0.58  fof(f97,plain,(
% 1.63/0.58    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl10_5),
% 1.63/0.58    inference(resolution,[],[f93,f48])).
% 1.63/0.58  fof(f48,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f106,plain,(
% 1.63/0.58    ~spl10_6 | ~spl10_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f98,f92,f104])).
% 1.63/0.58  fof(f98,plain,(
% 1.63/0.58    ~v1_xboole_0(k9_relat_1(sK3,sK2)) | ~spl10_5),
% 1.63/0.58    inference(resolution,[],[f93,f55])).
% 1.63/0.58  fof(f94,plain,(
% 1.63/0.58    spl10_5 | ~spl10_2 | ~spl10_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f90,f87,f63,f92])).
% 1.63/0.58  fof(f87,plain,(
% 1.63/0.58    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.63/0.58  fof(f90,plain,(
% 1.63/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_2 | ~spl10_4)),
% 1.63/0.58    inference(forward_demodulation,[],[f88,f66])).
% 1.63/0.58  fof(f88,plain,(
% 1.63/0.58    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 1.63/0.58    inference(avatar_component_clause,[],[f87])).
% 1.63/0.58  fof(f89,plain,(
% 1.63/0.58    spl10_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f31,f87])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.63/0.58    inference(cnf_transformation,[],[f17])).
% 1.63/0.58  fof(f85,plain,(
% 1.63/0.58    spl10_3 | ~spl10_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f81,f63,f83])).
% 1.63/0.58  fof(f81,plain,(
% 1.63/0.58    v1_relat_1(sK3) | ~spl10_2),
% 1.63/0.58    inference(subsumption_resolution,[],[f74,f44])).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.63/0.58  fof(f74,plain,(
% 1.63/0.58    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl10_2),
% 1.63/0.58    inference(resolution,[],[f64,f53])).
% 1.63/0.58  fof(f53,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f4])).
% 1.63/0.58  fof(f4,axiom,(
% 1.63/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.63/0.58  fof(f65,plain,(
% 1.63/0.58    spl10_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f33,f63])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.58    inference(cnf_transformation,[],[f17])).
% 1.63/0.58  fof(f61,plain,(
% 1.63/0.58    spl10_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f32,f59])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    v1_funct_1(sK3)),
% 1.63/0.58    inference(cnf_transformation,[],[f17])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (19106)------------------------------
% 1.63/0.58  % (19106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (19106)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (19106)Memory used [KB]: 6396
% 1.63/0.58  % (19106)Time elapsed: 0.152 s
% 1.63/0.58  % (19106)------------------------------
% 1.63/0.58  % (19106)------------------------------
% 1.63/0.58  % (19105)Success in time 0.22 s
%------------------------------------------------------------------------------
