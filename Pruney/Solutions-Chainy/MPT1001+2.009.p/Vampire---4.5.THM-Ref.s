%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 221 expanded)
%              Number of leaves         :   29 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  303 ( 549 expanded)
%              Number of equality atoms :   67 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f89,f91,f113,f153,f190,f252,f287,f371,f377,f385,f399,f407,f414,f443])).

fof(f443,plain,
    ( ~ spl6_20
    | ~ spl6_5
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f439,f405,f76,f208])).

fof(f208,plain,
    ( spl6_20
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f76,plain,
    ( spl6_5
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f405,plain,
    ( spl6_35
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f439,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl6_5
    | ~ spl6_35 ),
    inference(resolution,[],[f406,f78])).

fof(f78,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0)) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f405])).

fof(f414,plain,
    ( spl6_20
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f412,f71,f58,f208])).

fof(f58,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f71,plain,
    ( spl6_4
  <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f412,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(superposition,[],[f184,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f184,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f60])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f407,plain,
    ( ~ spl6_6
    | spl6_35
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f398,f105,f405,f82])).

fof(f82,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f105,plain,
    ( spl6_8
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_8 ),
    inference(superposition,[],[f53,f107])).

fof(f107,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 != k10_relat_1(X1,k1_enumset1(X0,X0,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f399,plain,
    ( spl6_3
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f387,f110,f105,f66])).

fof(f66,plain,
    ( spl6_3
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f110,plain,
    ( spl6_9
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f387,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f112,f107])).

fof(f112,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f385,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f103,f66,f58,f105])).

fof(f103,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f102,f68])).

fof(f68,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f102,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f46,f60])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f377,plain,
    ( spl6_8
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f292,f170,f165,f105])).

fof(f165,plain,
    ( spl6_15
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f170,plain,
    ( spl6_16
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f292,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f172,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f172,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f371,plain,
    ( spl6_25
    | ~ spl6_6
    | spl6_15 ),
    inference(avatar_split_clause,[],[f354,f165,f82,f249])).

fof(f249,plain,
    ( spl6_25
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f354,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2)))
    | ~ spl6_6
    | spl6_15 ),
    inference(resolution,[],[f203,f167])).

fof(f167,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f203,plain,
    ( ! [X3] :
        ( r1_tarski(X3,k2_relat_1(sK2))
        | k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(X3,sK2),sK4(X3,sK2),sK4(X3,sK2))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f52,f84])).

fof(f84,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_enumset1(sK4(X0,X1),sK4(X0,X1),sK4(X0,X1)))
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f287,plain,
    ( spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f286,f187,f170])).

fof(f187,plain,
    ( spl6_17
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f286,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_17 ),
    inference(resolution,[],[f213,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f213,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k2_relat_1(sK2),X0),sK1)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl6_17 ),
    inference(resolution,[],[f191,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl6_17 ),
    inference(resolution,[],[f189,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f189,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f252,plain,
    ( spl6_15
    | ~ spl6_25
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f247,f82,f63,f58,f249,f165])).

fof(f63,plain,
    ( spl6_2
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f247,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2)))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(resolution,[],[f204,f100])).

fof(f100,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(X3,sK2),X3)
        | r1_tarski(X3,k2_relat_1(sK2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f35,f84])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f204,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X3,X3,X3)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f64,f184])).

fof(f64,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3)) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f190,plain,
    ( spl6_17
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f185,f150,f110,f187])).

fof(f150,plain,
    ( spl6_14
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f185,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f152,f112])).

fof(f152,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl6_14
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f140,f58,f150])).

fof(f140,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f47,f60])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f113,plain,
    ( spl6_9
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f102,f58,f110])).

fof(f91,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f88,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f88,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_7
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f89,plain,
    ( spl6_6
    | ~ spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f80,f58,f86,f82])).

fof(f80,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f32,f60])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f79,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f27,f66,f76])).

fof(f27,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

fof(f74,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f51,f66,f71])).

fof(f51,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f28,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f50,f66,f63])).

fof(f50,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3)) ) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f29,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (12491)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (12499)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (12499)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f61,f69,f74,f79,f89,f91,f113,f153,f190,f252,f287,f371,f377,f385,f399,f407,f414,f443])).
% 0.21/0.50  fof(f443,plain,(
% 0.21/0.50    ~spl6_20 | ~spl6_5 | ~spl6_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f439,f405,f76,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    spl6_20 <=> k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl6_5 <=> r2_hidden(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    spl6_35 <=> ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl6_5 | ~spl6_35)),
% 0.21/0.50    inference(resolution,[],[f406,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    r2_hidden(sK3,sK1) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0))) ) | ~spl6_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f405])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    spl6_20 | ~spl6_1 | ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f412,f71,f58,f208])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl6_4 <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl6_1 | ~spl6_4)),
% 0.21/0.50    inference(superposition,[],[f184,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3)) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f48,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    ~spl6_6 | spl6_35 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f398,f105,f405,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl6_6 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl6_8 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X0,X0,X0)) | ~v1_relat_1(sK2)) ) | ~spl6_8),
% 0.21/0.50    inference(superposition,[],[f53,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 != k10_relat_1(X1,k1_enumset1(X0,X0,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f38,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    spl6_3 | ~spl6_8 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f387,f110,f105,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl6_3 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl6_9 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | (~spl6_8 | ~spl6_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f112,f107])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    spl6_8 | ~spl6_1 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f66,f58,f105])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2) | (~spl6_1 | ~spl6_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f102,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f46,f60])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    spl6_8 | ~spl6_15 | ~spl6_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f292,f170,f165,f105])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl6_15 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl6_16 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~spl6_16),
% 0.21/0.50    inference(resolution,[],[f172,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f170])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    spl6_25 | ~spl6_6 | spl6_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f354,f165,f82,f249])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl6_25 <=> k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2))) | (~spl6_6 | spl6_15)),
% 0.21/0.50    inference(resolution,[],[f203,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl6_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X3] : (r1_tarski(X3,k2_relat_1(sK2)) | k1_xboole_0 = k10_relat_1(sK2,k1_enumset1(sK4(X3,sK2),sK4(X3,sK2),sK4(X3,sK2)))) ) | ~spl6_6),
% 0.21/0.50    inference(resolution,[],[f52,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k1_enumset1(sK4(X0,X1),sK4(X0,X1),sK4(X0,X1))) | r1_tarski(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f36,f49])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) | r1_tarski(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    spl6_16 | ~spl6_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f286,f187,f170])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl6_17 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~spl6_17),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f284])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | r1_tarski(k2_relat_1(sK2),sK1) | ~spl6_17),
% 0.21/0.50    inference(resolution,[],[f213,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK2),X0),sK1) | r1_tarski(k2_relat_1(sK2),X0)) ) | ~spl6_17),
% 0.21/0.50    inference(resolution,[],[f191,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | ~spl6_17),
% 0.21/0.50    inference(resolution,[],[f189,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl6_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    spl6_15 | ~spl6_25 | ~spl6_1 | ~spl6_2 | ~spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f247,f82,f63,f58,f249,f165])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl6_2 <=> ! [X3] : (~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(sK4(sK1,sK2),sK4(sK1,sK2),sK4(sK1,sK2))) | r1_tarski(sK1,k2_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_6)),
% 0.21/0.50    inference(resolution,[],[f204,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(sK4(X3,sK2),X3) | r1_tarski(X3,k2_relat_1(sK2))) ) | ~spl6_6),
% 0.21/0.50    inference(resolution,[],[f35,f84])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_xboole_0 != k10_relat_1(sK2,k1_enumset1(X3,X3,X3))) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.50    inference(backward_demodulation,[],[f64,f184])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3))) ) | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl6_17 | ~spl6_9 | ~spl6_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f185,f150,f110,f187])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl6_14 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl6_9 | ~spl6_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f152,f112])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl6_14 | ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f58,f150])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f47,f60])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl6_9 | ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f58,f110])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    $false | spl6_7),
% 0.21/0.50    inference(resolution,[],[f88,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl6_7 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl6_6 | ~spl6_7 | ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f80,f58,f86,f82])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f32,f60])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl6_5 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f66,f76])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl6_4 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f66,f71])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_enumset1(sK3,sK3,sK3))),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f49])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl6_2 | spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f66,f63])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_enumset1(X3,X3,X3))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f29,f49])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f58])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12499)------------------------------
% 0.21/0.50  % (12499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12499)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12499)Memory used [KB]: 11001
% 0.21/0.51  % (12499)Time elapsed: 0.085 s
% 0.21/0.51  % (12499)------------------------------
% 0.21/0.51  % (12499)------------------------------
% 0.21/0.51  % (12482)Success in time 0.143 s
%------------------------------------------------------------------------------
