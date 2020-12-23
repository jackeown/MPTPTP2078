%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 356 expanded)
%              Number of leaves         :   38 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  626 (2150 expanded)
%              Number of equality atoms :  128 ( 582 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f74,f81,f85,f89,f93,f97,f101,f107,f112,f124,f136,f166,f242,f250,f266,f288,f303,f314,f341,f346,f349,f353,f355,f358,f361,f362])).

fof(f362,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f361,plain,
    ( ~ spl6_31
    | ~ spl6_11
    | ~ spl6_32
    | ~ spl6_9
    | spl6_12
    | ~ spl6_38
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f360,f129,f60,f339,f105,f91,f257,f99,f254])).

fof(f254,plain,
    ( spl6_31
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f99,plain,
    ( spl6_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f257,plain,
    ( spl6_32
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f91,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f105,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f339,plain,
    ( spl6_38
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f60,plain,
    ( spl6_1
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f129,plain,
    ( spl6_15
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f359,f130])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f70,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f358,plain,
    ( ~ spl6_7
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl6_7
    | spl6_32 ),
    inference(subsumption_resolution,[],[f84,f356])).

fof(f356,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_32 ),
    inference(resolution,[],[f258,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f258,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f257])).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f355,plain,
    ( ~ spl6_10
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f96,f226])).

fof(f226,plain,
    ( ! [X4,X3] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl6_26
  <=> ! [X3,X4] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f353,plain,
    ( ~ spl6_31
    | ~ spl6_11
    | ~ spl6_32
    | ~ spl6_9
    | spl6_1
    | ~ spl6_38
    | ~ spl6_15
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f352,f295,f129,f339,f60,f91,f257,f99,f254])).

fof(f295,plain,
    ( spl6_35
  <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f352,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_15
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f351,f130])).

% (24536)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f351,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_35 ),
    inference(trivial_inequality_removal,[],[f350])).

fof(f350,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_35 ),
    inference(superposition,[],[f43,f296])).

fof(f296,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f295])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f349,plain,
    ( ~ spl6_10
    | spl6_39 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl6_10
    | spl6_39 ),
    inference(subsumption_resolution,[],[f96,f347])).

fof(f347,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl6_39 ),
    inference(resolution,[],[f345,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f345,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f344])).

% (24547)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f344,plain,
    ( spl6_39
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f346,plain,
    ( ~ spl6_39
    | spl6_38 ),
    inference(avatar_split_clause,[],[f342,f339,f344])).

fof(f342,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | spl6_38 ),
    inference(resolution,[],[f340,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f340,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f339])).

fof(f341,plain,
    ( spl6_1
    | ~ spl6_9
    | spl6_28
    | spl6_35
    | ~ spl6_38
    | ~ spl6_15
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f337,f229,f129,f339,f295,f233,f91,f60])).

fof(f233,plain,
    ( spl6_28
  <=> ! [X3,X4] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f229,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | r1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),sK0)
        | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3)
        | r1_partfun1(sK2,sK3) )
    | ~ spl6_15
    | ~ spl6_27 ),
    inference(superposition,[],[f230,f130])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK2,X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f314,plain,
    ( ~ spl6_23
    | spl6_20
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f184,f164,f158,f168])).

fof(f168,plain,
    ( spl6_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f158,plain,
    ( spl6_20
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f164,plain,
    ( spl6_22
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f184,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_22 ),
    inference(resolution,[],[f165,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f165,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f164])).

fof(f303,plain,
    ( spl6_26
    | ~ spl6_11
    | spl6_27
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f285,f105,f229,f99,f225])).

fof(f285,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl6_12 ),
    inference(resolution,[],[f106,f216])).

fof(f216,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f215,f45])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f42,f45])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f288,plain,
    ( spl6_2
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f286,f110,f105,f63])).

fof(f63,plain,
    ( spl6_2
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f110,plain,
    ( spl6_13
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f286,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(resolution,[],[f106,f111])).

fof(f111,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f266,plain,
    ( ~ spl6_10
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl6_10
    | spl6_31 ),
    inference(subsumption_resolution,[],[f96,f263])).

fof(f263,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_31 ),
    inference(resolution,[],[f255,f45])).

fof(f255,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f254])).

fof(f250,plain,
    ( spl6_23
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f249,f83,f79,f168])).

fof(f79,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f249,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f84,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f242,plain,
    ( ~ spl6_7
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f84,f234])).

fof(f234,plain,
    ( ! [X4,X3] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f166,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f140,f87,f79,f164])).

fof(f87,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f140,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f88,f80])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f136,plain,
    ( ~ spl6_7
    | spl6_15
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f127,f122,f129,f83])).

fof(f122,plain,
    ( spl6_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f127,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_14 ),
    inference(superposition,[],[f46,f123])).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( ~ spl6_7
    | spl6_5
    | spl6_14
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f118,f87,f122,f76,f83])).

fof(f76,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f118,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(resolution,[],[f48,f88])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,
    ( ~ spl6_10
    | spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f108,f67,f110,f95])).

fof(f67,plain,
    ( spl6_3
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f108,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(superposition,[],[f68,f46])).

fof(f68,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f107,plain,
    ( ~ spl6_10
    | spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f102,f72,f105,f95])).

fof(f72,plain,
    ( spl6_4
  <=> ! [X5] :
        ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_4 ),
    inference(superposition,[],[f73,f46])).

fof(f73,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f101,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f32,f99])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X5] :
          ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
                & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
            | r1_partfun1(sK2,X3) )
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (24550)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f24,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
              & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
          | ~ r1_partfun1(sK2,X3) )
        & ( ! [X5] :
              ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
          | r1_partfun1(sK2,X3) )
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ( ? [X4] :
            ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
            & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
        | ~ r1_partfun1(sK2,sK3) )
      & ( ! [X5] :
            ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
        | r1_partfun1(sK2,sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
        & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
   => ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f97,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f33,f95])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f37,f79,f76])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f38,f72,f60])).

fof(f38,plain,(
    ! [X5] :
      ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f39,f67,f60])).

fof(f39,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f40,f63,f60])).

fof(f40,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (24546)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (24538)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (24549)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (24540)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (24545)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (24534)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (24537)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (24538)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f363,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f65,f69,f74,f81,f85,f89,f93,f97,f101,f107,f112,f124,f136,f166,f242,f250,f266,f288,f303,f314,f341,f346,f349,f353,f355,f358,f361,f362])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    ~spl6_31 | ~spl6_11 | ~spl6_32 | ~spl6_9 | spl6_12 | ~spl6_38 | ~spl6_1 | ~spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f360,f129,f60,f339,f105,f91,f257,f99,f254])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    spl6_31 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl6_11 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    spl6_32 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl6_9 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl6_12 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    spl6_38 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl6_1 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl6_15 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl6_1 | ~spl6_15)),
% 0.22/0.50    inference(forward_demodulation,[],[f359,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f129])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f70,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r1_partfun1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    r1_partfun1(sK2,sK3) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ~spl6_7 | spl6_32),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    $false | (~spl6_7 | spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_32),
% 0.22/0.50    inference(resolution,[],[f258,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl6_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f257])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    ~spl6_10 | ~spl6_26),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f354])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    $false | (~spl6_10 | ~spl6_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f226])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl6_26 <=> ! [X3,X4] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl6_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    ~spl6_31 | ~spl6_11 | ~spl6_32 | ~spl6_9 | spl6_1 | ~spl6_38 | ~spl6_15 | ~spl6_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f352,f295,f129,f339,f60,f91,f257,f99,f254])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    spl6_35 <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_15 | ~spl6_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f351,f130])).
% 0.22/0.50  % (24536)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_35),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f350])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_35),
% 0.22/0.50    inference(superposition,[],[f43,f296])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~spl6_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f295])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    ~spl6_10 | spl6_39),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f348])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    $false | (~spl6_10 | spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f347])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl6_39),
% 0.22/0.50    inference(resolution,[],[f345,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(superposition,[],[f47,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | spl6_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f344])).
% 0.22/0.50  % (24547)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    spl6_39 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.50  fof(f346,plain,(
% 0.22/0.50    ~spl6_39 | spl6_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f342,f339,f344])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | spl6_38),
% 0.22/0.50    inference(resolution,[],[f340,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | spl6_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f339])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    spl6_1 | ~spl6_9 | spl6_28 | spl6_35 | ~spl6_38 | ~spl6_15 | ~spl6_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f337,f229,f129,f339,f295,f233,f91,f60])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    spl6_28 <=> ! [X3,X4] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    spl6_27 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | r1_partfun1(sK2,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | r1_partfun1(sK2,sK3)) ) | (~spl6_15 | ~spl6_27)),
% 0.22/0.50    inference(superposition,[],[f230,f130])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | r1_partfun1(sK2,X0)) ) | ~spl6_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f229])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ~spl6_23 | spl6_20 | ~spl6_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f184,f164,f158,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl6_23 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl6_20 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl6_22 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_22),
% 0.22/0.50    inference(resolution,[],[f165,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl6_26 | ~spl6_11 | spl6_27 | ~spl6_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f285,f105,f229,f99,f225])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~v1_funct_1(X0) | r1_partfun1(sK2,X0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_12),
% 0.22/0.50    inference(resolution,[],[f106,f216])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | r1_partfun1(X0,X1) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.22/0.50    inference(resolution,[],[f215,f45])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | r1_partfun1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.50    inference(resolution,[],[f42,f45])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | r1_partfun1(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    spl6_2 | ~spl6_12 | ~spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f286,f110,f105,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl6_2 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl6_13 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | (~spl6_12 | ~spl6_13)),
% 0.22/0.50    inference(resolution,[],[f106,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ~spl6_10 | spl6_31),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    $false | (~spl6_10 | spl6_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f263])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_31),
% 0.22/0.50    inference(resolution,[],[f255,f45])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl6_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f254])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl6_23 | ~spl6_6 | ~spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f249,f83,f79,f168])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl6_6 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_6 | ~spl6_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f84,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f79])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~spl6_7 | ~spl6_28),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    $false | (~spl6_7 | ~spl6_28)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f234])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f233])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl6_22 | ~spl6_6 | ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f140,f87,f79,f164])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl6_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl6_6 | ~spl6_8)),
% 0.22/0.50    inference(superposition,[],[f88,f80])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ~spl6_7 | spl6_15 | ~spl6_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f127,f122,f129,f83])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl6_14 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_14),
% 0.22/0.50    inference(superposition,[],[f46,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~spl6_7 | spl6_5 | spl6_14 | ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f118,f87,f122,f76,f83])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f48,f88])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~spl6_10 | spl6_13 | ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f108,f67,f110,f95])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl6_3 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.50    inference(superposition,[],[f68,f46])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ~spl6_10 | spl6_12 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f102,f72,f105,f95])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl6_4 <=> ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl6_4),
% 0.22/0.50    inference(superposition,[],[f73,f46])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X5] : (~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f99])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (24550)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) => (k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.50    inference(rectify,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl6_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f95])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f91])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f87])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f83])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~spl6_5 | spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f79,f76])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl6_1 | spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f72,f60])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~spl6_1 | spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f67,f60])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~spl6_1 | ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f63,f60])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24538)------------------------------
% 0.22/0.50  % (24538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24538)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24538)Memory used [KB]: 10874
% 0.22/0.50  % (24538)Time elapsed: 0.025 s
% 0.22/0.50  % (24538)------------------------------
% 0.22/0.50  % (24538)------------------------------
% 0.22/0.51  % (24529)Success in time 0.144 s
%------------------------------------------------------------------------------
