%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0995+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 156 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 584 expanded)
%              Number of equality atoms :   61 ( 133 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f62,f66,f70,f74,f78,f90,f94,f99,f103,f107,f112,f152,f173])).

fof(f173,plain,
    ( ~ spl9_1
    | ~ spl9_8
    | spl9_10
    | ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_8
    | spl9_10
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f171,f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_10
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f171,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_1
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f170,f89])).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f170,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_1
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f168,f52])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f168,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_15 ),
    inference(resolution,[],[f151,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f151,plain,
    ( sP7(sK4,sK2,sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl9_15
  <=> sP7(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f152,plain,
    ( spl9_15
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f134,f109,f72,f60,f56,f150])).

fof(f56,plain,
    ( spl9_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f60,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f72,plain,
    ( spl9_6
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f109,plain,
    ( spl9_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f134,plain,
    ( sP7(sK4,sK2,sK3)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(resolution,[],[f127,f61])).

fof(f61,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(sK4,X0,sK3) )
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(forward_demodulation,[],[f125,f73])).

fof(f73,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP7(k1_funct_1(sK3,sK5),X0,sK3) )
    | ~ spl9_2
    | ~ spl9_13 ),
    inference(resolution,[],[f113,f57])).

fof(f57,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | sP7(k1_funct_1(sK3,X0),X1,sK3) )
    | ~ spl9_13 ),
    inference(superposition,[],[f44,f110])).

fof(f110,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | sP7(k1_funct_1(X0,X4),X1,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( spl9_13
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f111,f105,f101,f109])).

fof(f101,plain,
    ( spl9_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f105,plain,
    ( spl9_12
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f111,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f106,f102])).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f106,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl9_12
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f80,f76,f105])).

fof(f76,plain,
    ( spl9_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f80,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f103,plain,
    ( spl9_11
    | spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f86,f76,f68,f64,f101])).

fof(f64,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f68,plain,
    ( spl9_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f86,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f85,f69])).

fof(f69,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f82,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl9_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_7 ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f99,plain,
    ( ~ spl9_10
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f95,f92,f76,f97])).

fof(f92,plain,
    ( spl9_9
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f95,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_7
    | spl9_9 ),
    inference(forward_demodulation,[],[f93,f83])).

fof(f83,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl9_7 ),
    inference(resolution,[],[f77,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f20,f92])).

fof(f20,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

fof(f90,plain,
    ( spl9_8
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f79,f76,f88])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f78,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f23,f76])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f19,f72])).

fof(f19,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f22,f68])).

fof(f22,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f18,f60])).

fof(f18,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f17,f56])).

fof(f17,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
