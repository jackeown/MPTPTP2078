%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t17_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 170 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 ( 425 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f75,f82,f89,f96,f103,f113,f122,f152,f154,f164,f176,f185,f211,f217])).

fof(f217,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f215,f121])).

fof(f121,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_15
  <=> ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f215,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(resolution,[],[f214,f74])).

fof(f74,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(sK4,k2_zfmisc_1(X0,sK3)) )
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(resolution,[],[f212,f81])).

fof(f81,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_4
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(sK0,X1)
        | r1_tarski(sK4,k2_zfmisc_1(X1,X0)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f60,f129])).

fof(f129,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),X2)
        | r1_tarski(sK4,X2) )
    | ~ spl6_12 ),
    inference(resolution,[],[f58,f112])).

fof(f112,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_12
  <=> r1_tarski(sK4,k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t1_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t119_zfmisc_1)).

fof(f211,plain,
    ( ~ spl6_27
    | spl6_28
    | spl6_30
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f137,f94,f209,f203,f197])).

fof(f197,plain,
    ( spl6_27
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f203,plain,
    ( spl6_28
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f209,plain,
    ( spl6_30
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f94,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f137,plain,
    ( v1_xboole_0(sK4)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)),sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f131,f95])).

fof(f95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f125,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t2_subset)).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',antisymmetry_r2_hidden)).

fof(f185,plain,
    ( spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f169,f162,f183])).

fof(f183,plain,
    ( spl6_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f162,plain,
    ( spl6_20
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f169,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_20 ),
    inference(superposition,[],[f49,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f10,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',existence_m1_subset_1)).

fof(f176,plain,
    ( spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f167,f162,f174])).

fof(f174,plain,
    ( spl6_22
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f167,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_20 ),
    inference(superposition,[],[f105,f163])).

fof(f105,plain,(
    ! [X0] : r1_tarski(sK5(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t3_subset)).

fof(f164,plain,
    ( spl6_20
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f157,f150,f162])).

fof(f150,plain,
    ( spl6_18
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f157,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_18 ),
    inference(resolution,[],[f151,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t6_boole)).

fof(f151,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f154,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl6_16 ),
    inference(resolution,[],[f145,f49])).

fof(f145,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_16
  <=> ! [X0] : ~ m1_subset_1(X0,sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f152,plain,
    ( spl6_16
    | spl6_18
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f139,f66,f150,f144])).

fof(f66,plain,
    ( spl6_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f139,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X0,sK5(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl6_0 ),
    inference(resolution,[],[f134,f49])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl6_0 ),
    inference(resolution,[],[f133,f52])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_0 ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f66])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t5_subset)).

fof(f122,plain,
    ( ~ spl6_15
    | spl6_11 ),
    inference(avatar_split_clause,[],[f114,f101,f120])).

fof(f101,plain,
    ( spl6_11
  <=> ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f114,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK3))
    | ~ spl6_11 ),
    inference(resolution,[],[f54,f102])).

fof(f102,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,
    ( spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f106,f94,f111])).

fof(f106,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_8 ),
    inference(resolution,[],[f53,f95])).

fof(f103,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t17_relset_1)).

fof(f96,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f87,plain,
    ( spl6_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f47,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',d2_xboole_0)).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f61,f66])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
