%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 146 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 309 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f999,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f77,f90,f102,f110,f154,f169,f199,f223,f231,f987,f998])).

fof(f998,plain,
    ( k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)))
    | m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))
    | ~ m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f987,plain,
    ( spl3_40
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f967,f227,f106,f984])).

fof(f984,plain,
    ( spl3_40
  <=> m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f106,plain,
    ( spl3_7
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f227,plain,
    ( spl3_21
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f967,plain,
    ( m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f173,f240,f206])).

fof(f206,plain,(
    ! [X10,X8,X9] :
      ( m1_subset_1(k5_xboole_0(X10,k4_xboole_0(X8,X10)),k1_zfmisc_1(X9))
      | ~ r1_tarski(X10,X9)
      | ~ r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f240,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k5_xboole_0(X0,k4_xboole_0(sK1,X0)))
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f229,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f229,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f173,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(X0,sK0)))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f52,f108,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f108,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f231,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f225,f220,f227])).

fof(f220,plain,
    ( spl3_20
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f225,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f222,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f222,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( spl3_20
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f218,f165,f150,f220])).

fof(f150,plain,
    ( spl3_12
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f165,plain,
    ( spl3_14
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f218,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f167,f152])).

fof(f152,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f167,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f199,plain,
    ( spl3_17
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f193,f87,f195])).

fof(f195,plain,
    ( spl3_17
  <=> k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f87,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f193,plain,
    ( k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)))
    | ~ spl3_5 ),
    inference(resolution,[],[f51,f89])).

fof(f89,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f169,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f163,f61,f165])).

fof(f61,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f163,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f154,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f148,f61,f150])).

fof(f148,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f63])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f110,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f104,f98,f106,f87])).

fof(f98,plain,
    ( spl3_6
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f104,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f100,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f100,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f102,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f61,f98])).

fof(f96,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f63])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f84,f61,f87])).

fof(f84,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f36,f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f65,f56,f74])).

fof(f74,plain,
    ( spl3_4
  <=> m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( ~ m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f58,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f56])).

fof(f50,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (25784)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.44  % (25784)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f999,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f59,f64,f77,f90,f102,f110,f154,f169,f199,f223,f231,f987,f998])).
% 0.21/0.44  fof(f998,plain,(
% 0.21/0.44    k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) | m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) | ~m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f987,plain,(
% 0.21/0.44    spl3_40 | ~spl3_7 | ~spl3_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f967,f227,f106,f984])).
% 0.21/0.44  fof(f984,plain,(
% 0.21/0.44    spl3_40 <=> m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl3_7 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    spl3_21 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.44  fof(f967,plain,(
% 0.21/0.44    m1_subset_1(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) | (~spl3_7 | ~spl3_21)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f173,f240,f206])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    ( ! [X10,X8,X9] : (m1_subset_1(k5_xboole_0(X10,k4_xboole_0(X8,X10)),k1_zfmisc_1(X9)) | ~r1_tarski(X10,X9) | ~r1_tarski(X8,X9)) )),
% 0.21/0.44    inference(resolution,[],[f54,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f49,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k5_xboole_0(X0,k4_xboole_0(sK1,X0)))) ) | ~spl3_21),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f229,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f43,f38])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.44  fof(f229,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f227])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(X0,sK0)))) ) | ~spl3_7),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f52,f108,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f37,f38])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    spl3_21 | ~spl3_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f225,f220,f227])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    spl3_20 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_20),
% 0.21/0.44    inference(resolution,[],[f222,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f220])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    spl3_20 | ~spl3_12 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f218,f165,f150,f220])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    spl3_12 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl3_14 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl3_12 | ~spl3_14)),
% 0.21/0.44    inference(forward_demodulation,[],[f167,f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f150])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f165])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    spl3_17 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f193,f87,f195])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    spl3_17 <=> k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f193,plain,(
% 0.21/0.44    k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) | ~spl3_5),
% 0.21/0.44    inference(resolution,[],[f51,f89])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f34,f38])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    spl3_14 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f163,f61,f165])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl3_2),
% 0.21/0.44    inference(resolution,[],[f45,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    spl3_12 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f148,f61,f150])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_2),
% 0.21/0.44    inference(resolution,[],[f44,f63])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ~spl3_5 | spl3_7 | ~spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f104,f98,f106,f87])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl3_6 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f100,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    v4_relat_1(sK2,sK0) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f98])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_6 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f96,f61,f98])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    v4_relat_1(sK2,sK0) | ~spl3_2),
% 0.21/0.45    inference(resolution,[],[f46,f63])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl3_5 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f84,f61,f87])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f36,f63,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ~spl3_4 | spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f65,f56,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl3_4 <=> m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl3_1 <=> r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ~m1_subset_1(k3_relat_1(sK2),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) | spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f58,f41])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ~r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f61])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f14])).
% 0.21/0.45  fof(f14,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f50,f56])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f38])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (25784)------------------------------
% 0.21/0.45  % (25784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (25784)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (25784)Memory used [KB]: 6908
% 0.21/0.45  % (25784)Time elapsed: 0.029 s
% 0.21/0.45  % (25784)------------------------------
% 0.21/0.45  % (25784)------------------------------
% 0.21/0.45  % (25777)Success in time 0.086 s
%------------------------------------------------------------------------------
