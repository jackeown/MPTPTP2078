%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 147 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  264 ( 482 expanded)
%              Number of equality atoms :   29 (  77 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f77,f86,f90,f97,f106,f112,f128,f134,f137,f167,f171])).

fof(f171,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f27,f166])).

fof(f166,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_18
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f167,plain,
    ( ~ spl5_18
    | ~ spl5_10
    | spl5_13 ),
    inference(avatar_split_clause,[],[f156,f125,f100,f164])).

fof(f100,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f125,plain,
    ( spl5_13
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f156,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_10
    | spl5_13 ),
    inference(forward_demodulation,[],[f126,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f126,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f137,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_7
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f81,f76,f133,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_14
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f76,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_6
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f134,plain,
    ( spl5_9
    | ~ spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f129,f125,f131,f94])).

fof(f94,plain,
    ( spl5_9
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f129,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f127,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f128,plain,
    ( spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f123,f110,f125])).

fof(f110,plain,
    ( spl5_12
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f123,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_12 ),
    inference(resolution,[],[f116,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2)) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f113,f21])).

fof(f21,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK4(X0,k2_relat_1(sK2))),sK0)
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | r1_tarski(X0,k2_relat_1(sK2)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f111,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl5_3
    | spl5_12
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f108,f104,f110,f55])).

fof(f55,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f104,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f108,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl5_11 ),
    inference(superposition,[],[f105,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f105,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f98,f55,f50,f104,f100])).

fof(f50,plain,
    ( spl5_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(sK2,X1,X2)
      | r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f23,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f41,f22])).

fof(f22,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,
    ( ~ spl5_3
    | ~ spl5_9
    | spl5_4 ),
    inference(avatar_split_clause,[],[f72,f60,f94,f55])).

fof(f60,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f72,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_4 ),
    inference(superposition,[],[f62,f38])).

fof(f62,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f90,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f29,f85])).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_8
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f86,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f55,f83,f79])).

fof(f66,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f77,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f65,f55,f74])).

fof(f65,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f63,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3173)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (3189)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (3168)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (3180)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (3171)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (3169)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (3189)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f53,f58,f63,f77,f86,f90,f97,f106,f112,f128,f134,f137,f167,f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl5_18),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    $false | spl5_18),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f27,f166])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | spl5_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f164])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    spl5_18 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~spl5_18 | ~spl5_10 | spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f156,f125,f100,f164])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl5_10 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    spl5_13 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl5_10 | spl5_13)),
% 0.20/0.51    inference(forward_demodulation,[],[f126,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ~spl5_6 | ~spl5_7 | spl5_14),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    $false | (~spl5_6 | ~spl5_7 | spl5_14)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f81,f76,f133,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl5_14 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl5_6 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl5_7 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl5_9 | ~spl5_14 | ~spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f129,f125,f131,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl5_9 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK2),sK1) | sK1 = k2_relat_1(sK2) | ~spl5_13),
% 0.20/0.51    inference(resolution,[],[f127,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl5_13 | ~spl5_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f123,f110,f125])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl5_12 <=> ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_12),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_12),
% 0.20/0.51    inference(resolution,[],[f116,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2))) ) | ~spl5_12),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2)) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)) ) | ~spl5_12),
% 0.20/0.51    inference(resolution,[],[f113,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK3(sK4(X0,k2_relat_1(sK2))),sK0) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | r1_tarski(X0,k2_relat_1(sK2))) ) | ~spl5_12),
% 0.20/0.51    inference(resolution,[],[f111,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ~spl5_3 | spl5_12 | ~spl5_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f108,f104,f110,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl5_11 <=> ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl5_11),
% 0.20/0.51    inference(superposition,[],[f105,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0)) ) | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f104])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl5_10 | spl5_11 | ~spl5_2 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f98,f55,f50,f104,f100])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl5_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(sK3(X0),sK0) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK1)) ) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f92,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~r2_hidden(X0,sK1)) )),
% 0.20/0.51    inference(global_subsumption,[],[f23,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.51    inference(superposition,[],[f41,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ~spl5_3 | ~spl5_9 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f72,f60,f94,f55])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_4),
% 0.20/0.51    inference(superposition,[],[f62,f38])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f60])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl5_8),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    $false | spl5_8),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f29,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl5_8 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl5_7 | ~spl5_8 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f66,f55,f83,f79])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f57,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl5_6 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f65,f55,f74])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f57,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f60])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f55])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f50])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3189)------------------------------
% 0.20/0.51  % (3189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3189)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3189)Memory used [KB]: 10746
% 0.20/0.51  % (3189)Time elapsed: 0.058 s
% 0.20/0.51  % (3189)------------------------------
% 0.20/0.51  % (3189)------------------------------
% 0.20/0.51  % (3174)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (3159)Success in time 0.16 s
%------------------------------------------------------------------------------
