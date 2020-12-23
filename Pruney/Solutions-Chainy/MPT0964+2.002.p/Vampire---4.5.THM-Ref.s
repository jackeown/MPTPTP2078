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
% DateTime   : Thu Dec  3 13:00:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  306 ( 568 expanded)
%              Number of equality atoms :   88 ( 130 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f84,f89,f98,f106,f120,f123,f128])).

fof(f128,plain,
    ( spl7_8
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f126,f118,f65,f87])).

fof(f87,plain,
    ( spl7_8
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f65,plain,
    ( spl7_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f118,plain,
    ( spl7_13
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f126,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(resolution,[],[f119,f66])).

fof(f66,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3)) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f123,plain,
    ( ~ spl7_4
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl7_4
    | spl7_11 ),
    inference(subsumption_resolution,[],[f70,f121])).

fof(f121,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_11 ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f70,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f120,plain,
    ( ~ spl7_11
    | ~ spl7_6
    | spl7_13
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f108,f103,f118,f77,f110])).

fof(f77,plain,
    ( spl7_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f103,plain,
    ( spl7_10
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_10 ),
    inference(superposition,[],[f48,f104])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f48,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f106,plain,
    ( ~ spl7_4
    | spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f100,f94,f103,f69])).

fof(f94,plain,
    ( spl7_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f100,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_9 ),
    inference(superposition,[],[f39,f95])).

fof(f95,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,
    ( spl7_9
    | spl7_2
    | ~ spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f92,f69,f73,f61,f94])).

fof(f61,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f73,plain,
    ( spl7_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f41,f70])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f89,plain,
    ( ~ spl7_8
    | spl7_1
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f85,f82,f57,f87])).

fof(f57,plain,
    ( spl7_1
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f82,plain,
    ( spl7_7
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f85,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | spl7_1
    | ~ spl7_7 ),
    inference(superposition,[],[f58,f83])).

fof(f83,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f58,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f84,plain,
    ( spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f80,f69,f82])).

fof(f80,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f40,f70])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f79,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f75,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:19:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (5176)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (5174)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (5175)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (5182)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (5174)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (5183)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f84,f89,f98,f106,f120,f123,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl7_8 | ~spl7_3 | ~spl7_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f126,f118,f65,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl7_8 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl7_3 <=> r2_hidden(sK2,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl7_13 <=> ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl7_3 | ~spl7_13)),
% 0.22/0.52    inference(resolution,[],[f119,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0) | ~spl7_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f65])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3))) ) | ~spl7_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ~spl7_4 | spl7_11),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    $false | (~spl7_4 | spl7_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f70,f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_11),
% 0.22/0.52    inference(resolution,[],[f111,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | spl7_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl7_11 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl7_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ~spl7_11 | ~spl7_6 | spl7_13 | ~spl7_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f108,f103,f118,f77,f110])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl7_6 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl7_10 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl7_10),
% 0.22/0.52    inference(superposition,[],[f48,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | ~spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f103])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X6,X0] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ~spl7_4 | spl7_10 | ~spl7_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f100,f94,f103,f69])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl7_9 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_9),
% 0.22/0.52    inference(superposition,[],[f39,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f94])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl7_9 | spl7_2 | ~spl7_5 | ~spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f92,f69,f73,f61,f94])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl7_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_4),
% 0.22/0.52    inference(resolution,[],[f41,f70])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ~spl7_8 | spl7_1 | ~spl7_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f82,f57,f87])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl7_1 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl7_7 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (spl7_1 | ~spl7_7)),
% 0.22/0.52    inference(superposition,[],[f58,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl7_7 | ~spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f69,f82])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_4),
% 0.22/0.52    inference(resolution,[],[f40,f70])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl7_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f77])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f6])).
% 0.22/0.52  fof(f6,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl7_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f73])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f69])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl7_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f65])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f61])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (5174)------------------------------
% 0.22/0.52  % (5174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5174)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (5174)Memory used [KB]: 10618
% 0.22/0.52  % (5174)Time elapsed: 0.071 s
% 0.22/0.52  % (5174)------------------------------
% 0.22/0.52  % (5174)------------------------------
% 0.22/0.52  % (5167)Success in time 0.152 s
%------------------------------------------------------------------------------
