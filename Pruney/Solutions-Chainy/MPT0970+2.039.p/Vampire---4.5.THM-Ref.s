%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:54 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 152 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  286 ( 514 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f72,f85,f90,f100,f113,f132,f193,f222,f266,f292])).

fof(f292,plain,(
    ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f30,f221,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f221,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_20
  <=> r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f266,plain,
    ( spl6_6
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl6_6
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f84,f112,f112,f261])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl6_18 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) )
    | ~ spl6_18 ),
    inference(resolution,[],[f249,f24])).

fof(f24,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK4(X0,k2_relat_1(sK2))),sK0)
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
        | ~ r2_hidden(sK4(X0,k2_relat_1(sK2)),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl6_18 ),
    inference(resolution,[],[f192,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_18
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f112,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_10
  <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f84,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f222,plain,
    ( spl6_20
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f207,f126,f110,f219])).

fof(f126,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f207,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f112,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f193,plain,
    ( ~ spl6_3
    | spl6_18
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f188,f130,f191,f57])).

fof(f57,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f130,plain,
    ( spl6_14
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f188,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_14 ),
    inference(superposition,[],[f131,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f86,f57,f52,f130,f126])).

fof(f52,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
        | ~ r2_hidden(sK3(X0),sK0)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(sK2,X1,X2)
      | r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f26,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X2
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f42,f25])).

fof(f25,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,
    ( spl6_6
    | spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f108,f98,f110,f82])).

fof(f98,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f108,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl6_8 ),
    inference(factoring,[],[f102])).

fof(f102,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(X2,k2_relat_1(sK2)),sK1)
        | r2_hidden(sK4(X2,k2_relat_1(sK2)),X2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl6_8 ),
    inference(resolution,[],[f99,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( ~ spl6_5
    | spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f95,f88,f98,f69])).

fof(f69,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f88,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_7 ),
    inference(superposition,[],[f89,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(X0,sK1) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( ~ spl6_5
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f80,f57,f88,f69])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f78,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
        | r2_hidden(X4,sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f67,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f59,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f85,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | spl6_4 ),
    inference(avatar_split_clause,[],[f73,f62,f82,f57])).

fof(f62,plain,
    ( spl6_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f73,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_4 ),
    inference(superposition,[],[f64,f41])).

fof(f64,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f72,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f66,f57,f69])).

fof(f66,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f65,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (26397)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (26397)Refutation not found, incomplete strategy% (26397)------------------------------
% 0.21/0.52  % (26397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26404)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (26414)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (26388)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (26397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26397)Memory used [KB]: 10618
% 0.21/0.54  % (26397)Time elapsed: 0.082 s
% 0.21/0.54  % (26397)------------------------------
% 0.21/0.54  % (26397)------------------------------
% 0.21/0.54  % (26387)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.57  % (26406)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.57  % (26402)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.62/0.57  % (26394)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.62/0.58  % (26389)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.62/0.58  % (26412)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.58  % (26393)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.58  % (26395)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.59  % (26390)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.59  % (26411)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.59  % (26418)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.59  % (26417)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.59  % (26401)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.62/0.59  % (26391)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.62/0.60  % (26398)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.62/0.60  % (26413)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.60  % (26398)Refutation not found, incomplete strategy% (26398)------------------------------
% 1.62/0.60  % (26398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (26398)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (26398)Memory used [KB]: 10746
% 1.62/0.60  % (26398)Time elapsed: 0.171 s
% 1.62/0.60  % (26398)------------------------------
% 1.62/0.60  % (26398)------------------------------
% 1.62/0.60  % (26410)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.62/0.60  % (26416)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.61  % (26407)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.62/0.61  % (26409)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.62/0.61  % (26399)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.62  % (26411)Refutation found. Thanks to Tanya!
% 1.62/0.62  % SZS status Theorem for theBenchmark
% 1.62/0.62  % (26396)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.62/0.62  % (26415)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.06/0.63  % (26400)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.06/0.63  % (26392)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.06/0.63  % (26405)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.06/0.63  % (26405)Refutation not found, incomplete strategy% (26405)------------------------------
% 2.06/0.63  % (26405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (26405)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.63  
% 2.06/0.63  % (26405)Memory used [KB]: 10618
% 2.06/0.63  % (26405)Time elapsed: 0.206 s
% 2.06/0.63  % (26405)------------------------------
% 2.06/0.63  % (26405)------------------------------
% 2.06/0.64  % SZS output start Proof for theBenchmark
% 2.06/0.64  fof(f293,plain,(
% 2.06/0.64    $false),
% 2.06/0.64    inference(avatar_sat_refutation,[],[f55,f60,f65,f72,f85,f90,f100,f113,f132,f193,f222,f266,f292])).
% 2.06/0.64  fof(f292,plain,(
% 2.06/0.64    ~spl6_20),
% 2.06/0.64    inference(avatar_contradiction_clause,[],[f291])).
% 2.06/0.64  fof(f291,plain,(
% 2.06/0.64    $false | ~spl6_20),
% 2.06/0.64    inference(unit_resulting_resolution,[],[f30,f221,f35])).
% 2.06/0.64  fof(f35,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f18])).
% 2.06/0.64  fof(f18,plain,(
% 2.06/0.64    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.06/0.64    inference(ennf_transformation,[],[f7])).
% 2.06/0.64  fof(f7,axiom,(
% 2.06/0.64    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.06/0.64  fof(f221,plain,(
% 2.06/0.64    r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | ~spl6_20),
% 2.06/0.64    inference(avatar_component_clause,[],[f219])).
% 2.06/0.64  fof(f219,plain,(
% 2.06/0.64    spl6_20 <=> r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.06/0.64  fof(f30,plain,(
% 2.06/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f2])).
% 2.06/0.64  fof(f2,axiom,(
% 2.06/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.06/0.64  fof(f266,plain,(
% 2.06/0.64    spl6_6 | ~spl6_10 | ~spl6_18),
% 2.06/0.64    inference(avatar_contradiction_clause,[],[f262])).
% 2.06/0.64  fof(f262,plain,(
% 2.06/0.64    $false | (spl6_6 | ~spl6_10 | ~spl6_18)),
% 2.06/0.64    inference(unit_resulting_resolution,[],[f84,f112,f112,f261])).
% 2.06/0.64  fof(f261,plain,(
% 2.06/0.64    ( ! [X0] : (~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) ) | ~spl6_18),
% 2.06/0.64    inference(duplicate_literal_removal,[],[f260])).
% 2.06/0.64  fof(f260,plain,(
% 2.06/0.64    ( ! [X0] : (~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)) ) | ~spl6_18),
% 2.06/0.64    inference(resolution,[],[f249,f24])).
% 2.06/0.64  fof(f24,plain,(
% 2.06/0.64    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  fof(f14,plain,(
% 2.06/0.64    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.06/0.64    inference(flattening,[],[f13])).
% 2.06/0.64  fof(f13,plain,(
% 2.06/0.64    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.06/0.64    inference(ennf_transformation,[],[f12])).
% 2.06/0.64  fof(f12,negated_conjecture,(
% 2.06/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.06/0.64    inference(negated_conjecture,[],[f11])).
% 2.06/0.64  fof(f11,conjecture,(
% 2.06/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 2.06/0.64  fof(f249,plain,(
% 2.06/0.64    ( ! [X0] : (~r2_hidden(sK3(sK4(X0,k2_relat_1(sK2))),sK0) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | ~r2_hidden(sK4(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) ) | ~spl6_18),
% 2.06/0.64    inference(resolution,[],[f192,f34])).
% 2.06/0.64  fof(f34,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 2.06/0.64    inference(cnf_transformation,[],[f17])).
% 2.06/0.64  fof(f17,plain,(
% 2.06/0.64    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.06/0.64    inference(ennf_transformation,[],[f1])).
% 2.06/0.64  fof(f1,axiom,(
% 2.06/0.64    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.06/0.64  fof(f192,plain,(
% 2.06/0.64    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1)) ) | ~spl6_18),
% 2.06/0.64    inference(avatar_component_clause,[],[f191])).
% 2.06/0.64  fof(f191,plain,(
% 2.06/0.64    spl6_18 <=> ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1))),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.06/0.64  fof(f112,plain,(
% 2.06/0.64    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | ~spl6_10),
% 2.06/0.64    inference(avatar_component_clause,[],[f110])).
% 2.06/0.64  fof(f110,plain,(
% 2.06/0.64    spl6_10 <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.06/0.64  fof(f84,plain,(
% 2.06/0.64    sK1 != k2_relat_1(sK2) | spl6_6),
% 2.06/0.64    inference(avatar_component_clause,[],[f82])).
% 2.06/0.64  fof(f82,plain,(
% 2.06/0.64    spl6_6 <=> sK1 = k2_relat_1(sK2)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.06/0.64  fof(f222,plain,(
% 2.06/0.64    spl6_20 | ~spl6_10 | ~spl6_13),
% 2.06/0.64    inference(avatar_split_clause,[],[f207,f126,f110,f219])).
% 2.06/0.64  fof(f126,plain,(
% 2.06/0.64    spl6_13 <=> k1_xboole_0 = sK1),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.06/0.64  fof(f207,plain,(
% 2.06/0.64    r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | (~spl6_10 | ~spl6_13)),
% 2.06/0.64    inference(backward_demodulation,[],[f112,f128])).
% 2.06/0.64  fof(f128,plain,(
% 2.06/0.64    k1_xboole_0 = sK1 | ~spl6_13),
% 2.06/0.64    inference(avatar_component_clause,[],[f126])).
% 2.06/0.64  fof(f193,plain,(
% 2.06/0.64    ~spl6_3 | spl6_18 | ~spl6_14),
% 2.06/0.64    inference(avatar_split_clause,[],[f188,f130,f191,f57])).
% 2.06/0.64  fof(f57,plain,(
% 2.06/0.64    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.06/0.64  fof(f130,plain,(
% 2.06/0.64    spl6_14 <=> ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0))),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.06/0.64  fof(f188,plain,(
% 2.06/0.64    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl6_14),
% 2.06/0.64    inference(superposition,[],[f131,f41])).
% 2.06/0.64  fof(f41,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.64  fof(f21,plain,(
% 2.06/0.64    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.64    inference(ennf_transformation,[],[f9])).
% 2.06/0.64  fof(f9,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.06/0.64  fof(f131,plain,(
% 2.06/0.64    ( ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0)) ) | ~spl6_14),
% 2.06/0.64    inference(avatar_component_clause,[],[f130])).
% 2.06/0.64  fof(f132,plain,(
% 2.06/0.64    spl6_13 | spl6_14 | ~spl6_2 | ~spl6_3),
% 2.06/0.64    inference(avatar_split_clause,[],[f86,f57,f52,f130,f126])).
% 2.06/0.64  fof(f52,plain,(
% 2.06/0.64    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.06/0.64  fof(f86,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(sK3(X0),sK0) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK1)) ) | ~spl6_3),
% 2.06/0.64    inference(resolution,[],[f75,f59])).
% 2.06/0.64  fof(f59,plain,(
% 2.06/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 2.06/0.64    inference(avatar_component_clause,[],[f57])).
% 2.06/0.64  fof(f75,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~r2_hidden(X0,sK1)) )),
% 2.06/0.64    inference(global_subsumption,[],[f26,f74])).
% 2.06/0.64  fof(f74,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(sK3(X0),X1) | k1_xboole_0 = X2 | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 2.06/0.64    inference(superposition,[],[f42,f25])).
% 2.06/0.64  fof(f25,plain,(
% 2.06/0.64    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  fof(f42,plain,(
% 2.06/0.64    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f23])).
% 2.06/0.64  fof(f23,plain,(
% 2.06/0.64    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.06/0.64    inference(flattening,[],[f22])).
% 2.06/0.64  fof(f22,plain,(
% 2.06/0.64    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.06/0.64    inference(ennf_transformation,[],[f10])).
% 2.06/0.64  fof(f10,axiom,(
% 2.06/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 2.06/0.64  fof(f26,plain,(
% 2.06/0.64    v1_funct_1(sK2)),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  fof(f113,plain,(
% 2.06/0.64    spl6_6 | spl6_10 | ~spl6_8),
% 2.06/0.64    inference(avatar_split_clause,[],[f108,f98,f110,f82])).
% 2.06/0.64  fof(f98,plain,(
% 2.06/0.64    spl6_8 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1))),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.06/0.64  fof(f108,plain,(
% 2.06/0.64    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2) | ~spl6_8),
% 2.06/0.64    inference(factoring,[],[f102])).
% 2.06/0.64  fof(f102,plain,(
% 2.06/0.64    ( ! [X2] : (r2_hidden(sK4(X2,k2_relat_1(sK2)),sK1) | r2_hidden(sK4(X2,k2_relat_1(sK2)),X2) | k2_relat_1(sK2) = X2) ) | ~spl6_8),
% 2.06/0.64    inference(resolution,[],[f99,f33])).
% 2.06/0.64  fof(f33,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 2.06/0.64    inference(cnf_transformation,[],[f17])).
% 2.06/0.64  fof(f99,plain,(
% 2.06/0.64    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | ~spl6_8),
% 2.06/0.64    inference(avatar_component_clause,[],[f98])).
% 2.06/0.64  fof(f100,plain,(
% 2.06/0.64    ~spl6_5 | spl6_8 | ~spl6_7),
% 2.06/0.64    inference(avatar_split_clause,[],[f95,f88,f98,f69])).
% 2.06/0.64  fof(f69,plain,(
% 2.06/0.64    spl6_5 <=> v1_relat_1(sK2)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.06/0.64  fof(f88,plain,(
% 2.06/0.64    spl6_7 <=> ! [X1,X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k9_relat_1(sK2,X1)))),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.06/0.64  fof(f95,plain,(
% 2.06/0.64    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1) | ~v1_relat_1(sK2)) ) | ~spl6_7),
% 2.06/0.64    inference(superposition,[],[f89,f31])).
% 2.06/0.64  fof(f31,plain,(
% 2.06/0.64    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f15])).
% 2.06/0.64  fof(f15,plain,(
% 2.06/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.64    inference(ennf_transformation,[],[f6])).
% 2.06/0.64  fof(f6,axiom,(
% 2.06/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.06/0.64  fof(f89,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK2,X1)) | r2_hidden(X0,sK1)) ) | ~spl6_7),
% 2.06/0.64    inference(avatar_component_clause,[],[f88])).
% 2.06/0.64  fof(f90,plain,(
% 2.06/0.64    ~spl6_5 | spl6_7 | ~spl6_3),
% 2.06/0.64    inference(avatar_split_clause,[],[f80,f57,f88,f69])).
% 2.06/0.64  fof(f80,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) ) | ~spl6_3),
% 2.06/0.64    inference(resolution,[],[f78,f37])).
% 2.06/0.64  fof(f37,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f19])).
% 2.06/0.64  fof(f19,plain,(
% 2.06/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.06/0.64    inference(ennf_transformation,[],[f5])).
% 2.06/0.64  fof(f5,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 2.06/0.64  fof(f78,plain,(
% 2.06/0.64    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK2) | r2_hidden(X4,sK1)) ) | ~spl6_3),
% 2.06/0.64    inference(resolution,[],[f67,f44])).
% 2.06/0.64  fof(f44,plain,(
% 2.06/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f3])).
% 2.06/0.64  fof(f3,axiom,(
% 2.06/0.64    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.06/0.64  fof(f67,plain,(
% 2.06/0.64    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl6_3),
% 2.06/0.64    inference(resolution,[],[f59,f32])).
% 2.06/0.64  fof(f32,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f16])).
% 2.06/0.64  fof(f16,plain,(
% 2.06/0.64    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.64    inference(ennf_transformation,[],[f4])).
% 2.06/0.64  fof(f4,axiom,(
% 2.06/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.06/0.64  fof(f85,plain,(
% 2.06/0.64    ~spl6_3 | ~spl6_6 | spl6_4),
% 2.06/0.64    inference(avatar_split_clause,[],[f73,f62,f82,f57])).
% 2.06/0.64  fof(f62,plain,(
% 2.06/0.64    spl6_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.06/0.64  fof(f73,plain,(
% 2.06/0.64    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_4),
% 2.06/0.64    inference(superposition,[],[f64,f41])).
% 2.06/0.64  fof(f64,plain,(
% 2.06/0.64    sK1 != k2_relset_1(sK0,sK1,sK2) | spl6_4),
% 2.06/0.64    inference(avatar_component_clause,[],[f62])).
% 2.06/0.64  fof(f72,plain,(
% 2.06/0.64    spl6_5 | ~spl6_3),
% 2.06/0.64    inference(avatar_split_clause,[],[f66,f57,f69])).
% 2.06/0.64  fof(f66,plain,(
% 2.06/0.64    v1_relat_1(sK2) | ~spl6_3),
% 2.06/0.64    inference(resolution,[],[f59,f40])).
% 2.06/0.64  fof(f40,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f20])).
% 2.06/0.64  fof(f20,plain,(
% 2.06/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.64    inference(ennf_transformation,[],[f8])).
% 2.06/0.64  fof(f8,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.06/0.64  fof(f65,plain,(
% 2.06/0.64    ~spl6_4),
% 2.06/0.64    inference(avatar_split_clause,[],[f29,f62])).
% 2.06/0.64  fof(f29,plain,(
% 2.06/0.64    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  fof(f60,plain,(
% 2.06/0.64    spl6_3),
% 2.06/0.64    inference(avatar_split_clause,[],[f28,f57])).
% 2.06/0.64  fof(f28,plain,(
% 2.06/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  fof(f55,plain,(
% 2.06/0.64    spl6_2),
% 2.06/0.64    inference(avatar_split_clause,[],[f27,f52])).
% 2.06/0.64  fof(f27,plain,(
% 2.06/0.64    v1_funct_2(sK2,sK0,sK1)),
% 2.06/0.64    inference(cnf_transformation,[],[f14])).
% 2.06/0.64  % SZS output end Proof for theBenchmark
% 2.06/0.64  % (26411)------------------------------
% 2.06/0.64  % (26411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.64  % (26411)Termination reason: Refutation
% 2.06/0.64  
% 2.06/0.64  % (26411)Memory used [KB]: 10874
% 2.06/0.64  % (26411)Time elapsed: 0.213 s
% 2.06/0.64  % (26411)------------------------------
% 2.06/0.64  % (26411)------------------------------
% 2.06/0.64  % (26382)Success in time 0.277 s
%------------------------------------------------------------------------------
