%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 242 expanded)
%              Number of leaves         :   33 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  402 (1181 expanded)
%              Number of equality atoms :   65 ( 224 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f98,f103,f108,f130,f215,f391,f402,f406,f469,f475,f480,f585,f590,f592])).

fof(f592,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f590,plain,
    ( spl6_39
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f539,f477,f80,f587])).

fof(f587,plain,
    ( spl6_39
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f80,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f477,plain,
    ( spl6_31
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f539,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f491,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f491,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f82,f479,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f479,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f477])).

fof(f82,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f585,plain,
    ( spl6_38
    | ~ spl6_4
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f537,f472,f80,f582])).

fof(f582,plain,
    ( spl6_38
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f472,plain,
    ( spl6_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f537,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_4
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f486,f48])).

fof(f486,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_4
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f82,f474,f59])).

fof(f474,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f472])).

fof(f480,plain,
    ( spl6_31
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f426,f110,f105,f477])).

fof(f105,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f110,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f426,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f418,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f418,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(superposition,[],[f107,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f475,plain,
    ( spl6_30
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f425,f110,f100,f472])).

fof(f100,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f425,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f417,f61])).

fof(f417,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(superposition,[],[f102,f111])).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f469,plain,
    ( spl6_12
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | spl6_17 ),
    inference(avatar_split_clause,[],[f413,f197,f100,f85,f65,f127])).

fof(f127,plain,
    ( spl6_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f65,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( spl6_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f197,plain,
    ( spl6_17
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f413,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8
    | spl6_17 ),
    inference(subsumption_resolution,[],[f412,f198])).

fof(f198,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f412,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f379,f102])).

fof(f379,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f146,f87])).

fof(f87,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f406,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f402,plain,
    ( spl6_26
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f392,f242,f197,f105,f100,f75,f70,f65,f399])).

fof(f399,plain,
    ( spl6_26
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f70,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f75,plain,
    ( spl6_3
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f242,plain,
    ( spl6_24
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f392,plain,
    ( sK2 = sK3
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f67,f72,f77,f199,f102,f107,f244,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f244,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f242])).

fof(f199,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f77,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f391,plain,
    ( spl6_24
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9
    | spl6_12 ),
    inference(avatar_split_clause,[],[f289,f127,f105,f90,f70,f242])).

fof(f90,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f289,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f72,f92,f107,f129,f53])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f92,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f215,plain,
    ( spl6_20
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f137,f105,f212])).

fof(f212,plain,
    ( spl6_20
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f137,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f107,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f130,plain,
    ( ~ spl6_12
    | spl6_10 ),
    inference(avatar_split_clause,[],[f119,f110,f127])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f112,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f112,plain,
    ( k1_xboole_0 != sK1
    | spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f108,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f41,f105])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f103,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f95,plain,
    ( spl6_7
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f44,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f78,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (1453)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.46  % (1453)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f593,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f98,f103,f108,f130,f215,f391,f402,f406,f469,f475,f480,f585,f590,f592])).
% 0.22/0.46  fof(f592,plain,(
% 0.22/0.46    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 0.22/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.46  fof(f590,plain,(
% 0.22/0.46    spl6_39 | ~spl6_4 | ~spl6_31),
% 0.22/0.46    inference(avatar_split_clause,[],[f539,f477,f80,f587])).
% 0.22/0.46  fof(f587,plain,(
% 0.22/0.46    spl6_39 <=> k1_xboole_0 = sK3),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.46  fof(f477,plain,(
% 0.22/0.46    spl6_31 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.46  fof(f539,plain,(
% 0.22/0.46    k1_xboole_0 = sK3 | (~spl6_4 | ~spl6_31)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f491,f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.46  fof(f491,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl6_4 | ~spl6_31)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f82,f479,f59])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.46  fof(f479,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_31),
% 0.22/0.46    inference(avatar_component_clause,[],[f477])).
% 0.22/0.46  fof(f82,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0) | ~spl6_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f80])).
% 0.22/0.46  fof(f585,plain,(
% 0.22/0.46    spl6_38 | ~spl6_4 | ~spl6_30),
% 0.22/0.46    inference(avatar_split_clause,[],[f537,f472,f80,f582])).
% 0.22/0.46  fof(f582,plain,(
% 0.22/0.46    spl6_38 <=> k1_xboole_0 = sK2),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.46  fof(f472,plain,(
% 0.22/0.46    spl6_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.46  fof(f537,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | (~spl6_4 | ~spl6_30)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f486,f48])).
% 0.22/0.46  fof(f486,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl6_4 | ~spl6_30)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f82,f474,f59])).
% 0.22/0.46  fof(f474,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f472])).
% 0.22/0.46  fof(f480,plain,(
% 0.22/0.46    spl6_31 | ~spl6_9 | ~spl6_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f426,f110,f105,f477])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.46  fof(f110,plain,(
% 0.22/0.46    spl6_10 <=> k1_xboole_0 = sK1),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.46  fof(f426,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_9 | ~spl6_10)),
% 0.22/0.46    inference(forward_demodulation,[],[f418,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.46    inference(flattening,[],[f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.46    inference(nnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.46  fof(f418,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_9 | ~spl6_10)),
% 0.22/0.46    inference(superposition,[],[f107,f111])).
% 0.22/0.46  fof(f111,plain,(
% 0.22/0.46    k1_xboole_0 = sK1 | ~spl6_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f110])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f105])).
% 0.22/0.46  fof(f475,plain,(
% 0.22/0.46    spl6_30 | ~spl6_8 | ~spl6_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f425,f110,f100,f472])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    spl6_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.46  fof(f425,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_10)),
% 0.22/0.46    inference(forward_demodulation,[],[f417,f61])).
% 0.22/0.46  fof(f417,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_8 | ~spl6_10)),
% 0.22/0.46    inference(superposition,[],[f102,f111])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f100])).
% 0.22/0.46  fof(f469,plain,(
% 0.22/0.46    spl6_12 | ~spl6_1 | ~spl6_5 | ~spl6_8 | spl6_17),
% 0.22/0.46    inference(avatar_split_clause,[],[f413,f197,f100,f85,f65,f127])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl6_12 <=> v1_xboole_0(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    spl6_1 <=> v1_funct_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl6_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.46  fof(f197,plain,(
% 0.22/0.46    spl6_17 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.46  fof(f413,plain,(
% 0.22/0.46    v1_xboole_0(sK1) | (~spl6_1 | ~spl6_5 | ~spl6_8 | spl6_17)),
% 0.22/0.46    inference(subsumption_resolution,[],[f412,f198])).
% 0.22/0.46  fof(f198,plain,(
% 0.22/0.46    ~v1_partfun1(sK2,sK0) | spl6_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f197])).
% 0.22/0.46  fof(f412,plain,(
% 0.22/0.46    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1) | (~spl6_1 | ~spl6_5 | ~spl6_8)),
% 0.22/0.46    inference(subsumption_resolution,[],[f379,f102])).
% 0.22/0.46  fof(f379,plain,(
% 0.22/0.46    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl6_1 | ~spl6_5)),
% 0.22/0.46    inference(resolution,[],[f146,f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    v1_funct_2(sK2,sK0,sK1) | ~spl6_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f85])).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl6_1),
% 0.22/0.46    inference(resolution,[],[f53,f67])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    v1_funct_1(sK2) | ~spl6_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f65])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.46    inference(flattening,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.46  fof(f406,plain,(
% 0.22/0.46    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.46  fof(f402,plain,(
% 0.22/0.46    spl6_26 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_8 | ~spl6_9 | ~spl6_17 | ~spl6_24),
% 0.22/0.46    inference(avatar_split_clause,[],[f392,f242,f197,f105,f100,f75,f70,f65,f399])).
% 0.22/0.46  fof(f399,plain,(
% 0.22/0.46    spl6_26 <=> sK2 = sK3),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl6_3 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.46  fof(f242,plain,(
% 0.22/0.46    spl6_24 <=> v1_partfun1(sK3,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.46  fof(f392,plain,(
% 0.22/0.46    sK2 = sK3 | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_8 | ~spl6_9 | ~spl6_17 | ~spl6_24)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f67,f72,f77,f199,f102,f107,f244,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.46    inference(flattening,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.46  fof(f244,plain,(
% 0.22/0.46    v1_partfun1(sK3,sK0) | ~spl6_24),
% 0.22/0.46    inference(avatar_component_clause,[],[f242])).
% 0.22/0.46  fof(f199,plain,(
% 0.22/0.46    v1_partfun1(sK2,sK0) | ~spl6_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f197])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    r1_partfun1(sK2,sK3) | ~spl6_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f70])).
% 0.22/0.46  fof(f391,plain,(
% 0.22/0.46    spl6_24 | ~spl6_2 | ~spl6_6 | ~spl6_9 | spl6_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f289,f127,f105,f90,f70,f242])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    spl6_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.46  fof(f289,plain,(
% 0.22/0.46    v1_partfun1(sK3,sK0) | (~spl6_2 | ~spl6_6 | ~spl6_9 | spl6_12)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f72,f92,f107,f129,f53])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    ~v1_xboole_0(sK1) | spl6_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f127])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl6_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f90])).
% 0.22/0.46  fof(f215,plain,(
% 0.22/0.46    spl6_20 | ~spl6_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f137,f105,f212])).
% 0.22/0.46  fof(f212,plain,(
% 0.22/0.46    spl6_20 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl6_9),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f107,f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.46    inference(condensation,[],[f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.46  fof(f130,plain,(
% 0.22/0.46    ~spl6_12 | spl6_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f119,f110,f127])).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    ~v1_xboole_0(sK1) | spl6_10),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f112,f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.46  fof(f112,plain,(
% 0.22/0.46    k1_xboole_0 != sK1 | spl6_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f110])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    spl6_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f41,f105])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.46    inference(flattening,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f12])).
% 0.22/0.46  fof(f12,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    spl6_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f38,f100])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ~spl6_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f44,f95])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl6_7 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl6_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f40,f90])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    spl6_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f37,f85])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl6_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f45,f80])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    spl6_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f75])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    r1_partfun1(sK2,sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl6_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f39,f70])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    v1_funct_1(sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    spl6_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    v1_funct_1(sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (1453)------------------------------
% 0.22/0.46  % (1453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (1453)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (1453)Memory used [KB]: 11001
% 0.22/0.46  % (1453)Time elapsed: 0.056 s
% 0.22/0.46  % (1453)------------------------------
% 0.22/0.46  % (1453)------------------------------
% 0.22/0.46  % (1429)Success in time 0.099 s
%------------------------------------------------------------------------------
