%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 254 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  461 ( 818 expanded)
%              Number of equality atoms :   72 ( 121 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f929,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f154,f173,f216,f385,f392,f419,f428,f442,f525,f571,f589,f665,f666,f675,f716,f895,f915,f926,f928])).

fof(f928,plain,
    ( ~ spl6_64
    | spl6_94 ),
    inference(avatar_split_clause,[],[f927,f924,f714])).

fof(f714,plain,
    ( spl6_64
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f924,plain,
    ( spl6_94
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f927,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | spl6_94 ),
    inference(resolution,[],[f925,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f925,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | spl6_94 ),
    inference(avatar_component_clause,[],[f924])).

fof(f926,plain,
    ( ~ spl6_94
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f922,f913,f924])).

fof(f913,plain,
    ( spl6_92
  <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f922,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_92 ),
    inference(trivial_inequality_removal,[],[f921])).

fof(f921,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_92 ),
    inference(superposition,[],[f58,f914])).

fof(f914,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f913])).

fof(f58,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f915,plain,
    ( ~ spl6_32
    | ~ spl6_4
    | spl6_92
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f901,f893,f913,f105,f398])).

fof(f398,plain,
    ( spl6_32
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f105,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f893,plain,
    ( spl6_89
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f901,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_89 ),
    inference(resolution,[],[f894,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f894,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f893])).

fof(f895,plain,
    ( spl6_89
    | ~ spl6_11
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f890,f587,f171,f893])).

fof(f171,plain,
    ( spl6_11
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f587,plain,
    ( spl6_61
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f890,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)
    | ~ spl6_11
    | ~ spl6_61 ),
    inference(resolution,[],[f588,f172])).

fof(f172,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f588,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f587])).

fof(f716,plain,
    ( spl6_64
    | ~ spl6_11
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f711,f439,f171,f714])).

fof(f439,plain,
    ( spl6_39
  <=> ! [X0] :
        ( r2_hidden(sK5(X0,sK1,sK3),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f711,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_11
    | ~ spl6_39 ),
    inference(resolution,[],[f440,f172])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,sK1,sK3),sK1) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f439])).

fof(f675,plain,
    ( spl6_51
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f674,f523,f152,f93,f531])).

fof(f531,plain,
    ( spl6_51
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f93,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f152,plain,
    ( spl6_10
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f523,plain,
    ( spl6_49
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f674,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_49 ),
    inference(resolution,[],[f524,f162])).

fof(f162,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X1))
        | r2_hidden(sK0,X1) )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(superposition,[],[f138,f153])).

fof(f153,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X0))
        | r2_hidden(sK0,X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f524,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f523])).

fof(f666,plain,
    ( ~ spl6_52
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f650,f531,f535])).

fof(f535,plain,
    ( spl6_52
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f650,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_51 ),
    inference(resolution,[],[f532,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

% (14307)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f532,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f531])).

fof(f665,plain,(
    spl6_52 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | spl6_52 ),
    inference(resolution,[],[f536,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f536,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl6_52 ),
    inference(avatar_component_clause,[],[f535])).

fof(f589,plain,
    ( spl6_38
    | spl6_61
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f585,f417,f587,f436])).

fof(f436,plain,
    ( spl6_38
  <=> ! [X1,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f417,plain,
    ( spl6_37
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f585,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X4,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
    | ~ spl6_37 ),
    inference(superposition,[],[f340,f418])).

fof(f418,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f340,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f69,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f571,plain,
    ( ~ spl6_2
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f98,f437])).

fof(f437,plain,
    ( ! [X2,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f436])).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f525,plain,
    ( spl6_49
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f464,f380,f214,f523])).

fof(f214,plain,
    ( spl6_17
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f380,plain,
    ( spl6_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f464,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(superposition,[],[f215,f381])).

fof(f381,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f380])).

fof(f215,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f214])).

fof(f442,plain,
    ( spl6_38
    | spl6_39
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f433,f417,f439,f436])).

fof(f433,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK3))
        | r2_hidden(sK5(X3,sK1,sK3),sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_37 ),
    inference(superposition,[],[f146,f418])).

fof(f146,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | r2_hidden(sK5(X0,X2,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f70,f72])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f428,plain,
    ( ~ spl6_2
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl6_2
    | spl6_32 ),
    inference(subsumption_resolution,[],[f98,f426])).

fof(f426,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_32 ),
    inference(resolution,[],[f399,f72])).

fof(f399,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f398])).

fof(f419,plain,
    ( ~ spl6_32
    | spl6_37
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f396,f389,f417,f398])).

fof(f389,plain,
    ( spl6_31
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f396,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl6_31 ),
    inference(superposition,[],[f60,f390])).

fof(f390,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f389])).

fof(f60,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f392,plain,
    ( ~ spl6_2
    | spl6_31
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f387,f383,f389,f97])).

fof(f383,plain,
    ( spl6_30
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f387,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_30 ),
    inference(superposition,[],[f73,f384])).

fof(f384,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f383])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f385,plain,
    ( ~ spl6_2
    | spl6_29
    | spl6_30
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f375,f101,f383,f380,f97])).

fof(f101,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f375,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f76,f102])).

fof(f102,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f216,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f212,f152,f97,f214])).

fof(f212,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f208,f153])).

fof(f208,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f75,f98])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f173,plain,
    ( spl6_11
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f155,f152,f93,f171])).

fof(f155,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(superposition,[],[f94,f153])).

fof(f154,plain,
    ( spl6_10
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f147,f97,f152])).

fof(f147,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f74,f98])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f107,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f54,f105])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f56,f97])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f57,f93])).

fof(f57,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (14301)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.43  % (14301)Refutation not found, incomplete strategy% (14301)------------------------------
% 0.21/0.43  % (14301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (14301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (14301)Memory used [KB]: 10618
% 0.21/0.43  % (14301)Time elapsed: 0.028 s
% 0.21/0.43  % (14301)------------------------------
% 0.21/0.43  % (14301)------------------------------
% 0.21/0.45  % (14300)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (14306)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (14313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (14306)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f929,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f154,f173,f216,f385,f392,f419,f428,f442,f525,f571,f589,f665,f666,f675,f716,f895,f915,f926,f928])).
% 0.21/0.48  fof(f928,plain,(
% 0.21/0.48    ~spl6_64 | spl6_94),
% 0.21/0.48    inference(avatar_split_clause,[],[f927,f924,f714])).
% 0.21/0.48  fof(f714,plain,(
% 0.21/0.48    spl6_64 <=> r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.21/0.48  fof(f924,plain,(
% 0.21/0.48    spl6_94 <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.21/0.48  fof(f927,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1,sK3),sK1) | spl6_94),
% 0.21/0.48    inference(resolution,[],[f925,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f925,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | spl6_94),
% 0.21/0.48    inference(avatar_component_clause,[],[f924])).
% 0.21/0.48  fof(f926,plain,(
% 0.21/0.48    ~spl6_94 | ~spl6_92),
% 0.21/0.48    inference(avatar_split_clause,[],[f922,f913,f924])).
% 0.21/0.48  fof(f913,plain,(
% 0.21/0.48    spl6_92 <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 0.21/0.48  fof(f922,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_92),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f921])).
% 0.21/0.48  fof(f921,plain,(
% 0.21/0.48    sK0 != sK0 | ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_92),
% 0.21/0.48    inference(superposition,[],[f58,f914])).
% 0.21/0.48  fof(f914,plain,(
% 0.21/0.48    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | ~spl6_92),
% 0.21/0.48    inference(avatar_component_clause,[],[f913])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.48  fof(f915,plain,(
% 0.21/0.48    ~spl6_32 | ~spl6_4 | spl6_92 | ~spl6_89),
% 0.21/0.48    inference(avatar_split_clause,[],[f901,f893,f913,f105,f398])).
% 0.21/0.48  fof(f398,plain,(
% 0.21/0.48    spl6_32 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl6_4 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f893,plain,(
% 0.21/0.48    spl6_89 <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 0.21/0.48  fof(f901,plain,(
% 0.21/0.48    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_89),
% 0.21/0.48    inference(resolution,[],[f894,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f894,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) | ~spl6_89),
% 0.21/0.48    inference(avatar_component_clause,[],[f893])).
% 0.21/0.48  fof(f895,plain,(
% 0.21/0.48    spl6_89 | ~spl6_11 | ~spl6_61),
% 0.21/0.48    inference(avatar_split_clause,[],[f890,f587,f171,f893])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl6_11 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f587,plain,(
% 0.21/0.48    spl6_61 <=> ! [X4] : (~r2_hidden(X4,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.21/0.48  fof(f890,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) | (~spl6_11 | ~spl6_61)),
% 0.21/0.48    inference(resolution,[],[f588,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f171])).
% 0.21/0.48  fof(f588,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3)) ) | ~spl6_61),
% 0.21/0.48    inference(avatar_component_clause,[],[f587])).
% 0.21/0.48  fof(f716,plain,(
% 0.21/0.48    spl6_64 | ~spl6_11 | ~spl6_39),
% 0.21/0.48    inference(avatar_split_clause,[],[f711,f439,f171,f714])).
% 0.21/0.48  fof(f439,plain,(
% 0.21/0.48    spl6_39 <=> ! [X0] : (r2_hidden(sK5(X0,sK1,sK3),sK1) | ~r2_hidden(X0,k2_relat_1(sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.48  fof(f711,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1,sK3),sK1) | (~spl6_11 | ~spl6_39)),
% 0.21/0.48    inference(resolution,[],[f440,f172])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,sK1,sK3),sK1)) ) | ~spl6_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f439])).
% 0.21/0.48  fof(f675,plain,(
% 0.21/0.48    spl6_51 | ~spl6_1 | ~spl6_10 | ~spl6_49),
% 0.21/0.48    inference(avatar_split_clause,[],[f674,f523,f152,f93,f531])).
% 0.21/0.48  fof(f531,plain,(
% 0.21/0.48    spl6_51 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl6_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl6_10 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f523,plain,(
% 0.21/0.48    spl6_49 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.48  fof(f674,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_xboole_0) | (~spl6_1 | ~spl6_10 | ~spl6_49)),
% 0.21/0.48    inference(resolution,[],[f524,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X1)) | r2_hidden(sK0,X1)) ) | (~spl6_1 | ~spl6_10)),
% 0.21/0.48    inference(superposition,[],[f138,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X0)) | r2_hidden(sK0,X0)) ) | ~spl6_1),
% 0.21/0.48    inference(resolution,[],[f65,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f524,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~spl6_49),
% 0.21/0.48    inference(avatar_component_clause,[],[f523])).
% 0.21/0.48  fof(f666,plain,(
% 0.21/0.48    ~spl6_52 | ~spl6_51),
% 0.21/0.48    inference(avatar_split_clause,[],[f650,f531,f535])).
% 0.21/0.48  fof(f535,plain,(
% 0.21/0.48    spl6_52 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.21/0.48  fof(f650,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl6_51),
% 0.21/0.48    inference(resolution,[],[f532,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(resolution,[],[f66,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  % (14307)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  fof(f532,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_xboole_0) | ~spl6_51),
% 0.21/0.48    inference(avatar_component_clause,[],[f531])).
% 0.21/0.48  fof(f665,plain,(
% 0.21/0.48    spl6_52),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f663])).
% 0.21/0.48  fof(f663,plain,(
% 0.21/0.48    $false | spl6_52),
% 0.21/0.48    inference(resolution,[],[f536,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f536,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | spl6_52),
% 0.21/0.48    inference(avatar_component_clause,[],[f535])).
% 0.21/0.48  fof(f589,plain,(
% 0.21/0.48    spl6_38 | spl6_61 | ~spl6_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f585,f417,f587,f436])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    spl6_38 <=> ! [X1,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    spl6_37 <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.48  fof(f585,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X4,sK1,sK3),X4),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) ) | ~spl6_37),
% 0.21/0.48    inference(superposition,[],[f340,f418])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~spl6_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f417])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.48    inference(resolution,[],[f69,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(rectify,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f571,plain,(
% 0.21/0.48    ~spl6_2 | ~spl6_38),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f570])).
% 0.21/0.48  fof(f570,plain,(
% 0.21/0.48    $false | (~spl6_2 | ~spl6_38)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f437])).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl6_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f436])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f525,plain,(
% 0.21/0.48    spl6_49 | ~spl6_17 | ~spl6_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f464,f380,f214,f523])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    spl6_17 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    spl6_29 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.48  fof(f464,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (~spl6_17 | ~spl6_29)),
% 0.21/0.48    inference(superposition,[],[f215,f381])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl6_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f380])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl6_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f214])).
% 0.21/0.48  fof(f442,plain,(
% 0.21/0.48    spl6_38 | spl6_39 | ~spl6_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f433,f417,f439,f436])).
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_relat_1(sK3)) | r2_hidden(sK5(X3,sK1,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl6_37),
% 0.21/0.48    inference(superposition,[],[f146,f418])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | r2_hidden(sK5(X0,X2,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.48    inference(resolution,[],[f70,f72])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f50])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    ~spl6_2 | spl6_32),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f427])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    $false | (~spl6_2 | spl6_32)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f426])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_32),
% 0.21/0.48    inference(resolution,[],[f399,f72])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | spl6_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f398])).
% 0.21/0.48  fof(f419,plain,(
% 0.21/0.48    ~spl6_32 | spl6_37 | ~spl6_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f396,f389,f417,f398])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl6_31 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | ~spl6_31),
% 0.21/0.48    inference(superposition,[],[f60,f390])).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~spl6_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f389])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    ~spl6_2 | spl6_31 | ~spl6_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f387,f383,f389,f97])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    spl6_30 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_30),
% 0.21/0.48    inference(superposition,[],[f73,f384])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f383])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~spl6_2 | spl6_29 | spl6_30 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f375,f101,f383,f380,f97])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl6_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f76,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl6_17 | ~spl6_2 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f212,f152,f97,f214])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | (~spl6_2 | ~spl6_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f208,f153])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f75,f98])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl6_11 | ~spl6_1 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f152,f93,f171])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl6_1 | ~spl6_10)),
% 0.21/0.49    inference(superposition,[],[f94,f153])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl6_10 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f147,f97,f152])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f74,f98])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f105])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f101])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f97])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f93])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (14306)------------------------------
% 0.21/0.49  % (14306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14306)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (14306)Memory used [KB]: 11257
% 0.21/0.49  % (14306)Time elapsed: 0.050 s
% 0.21/0.49  % (14306)------------------------------
% 0.21/0.49  % (14306)------------------------------
% 0.21/0.49  % (14299)Success in time 0.133 s
%------------------------------------------------------------------------------
