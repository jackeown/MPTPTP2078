%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 ( 559 expanded)
%              Number of equality atoms :   57 ( 121 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f81,f85,f91,f95,f99,f104,f114])).

fof(f114,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | spl6_10
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f112,f90])).

fof(f90,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_10
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f112,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(resolution,[],[f110,f53])).

fof(f53,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f109,f65])).

fof(f65,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_6
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f109,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK5),k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f107,f87])).

fof(f87,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))
    | ~ spl6_8 ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1))) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f106,f80])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1))) )
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f45,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1))) )
    | ~ spl6_13 ),
    inference(superposition,[],[f28,f102])).

fof(f102,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f104,plain,
    ( spl6_13
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f103,f97,f93,f101])).

fof(f93,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f97,plain,
    ( spl6_12
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f103,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f98,f94])).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f98,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl6_12
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f71,f68,f97])).

fof(f68,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f71,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_7 ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f95,plain,
    ( spl6_11
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f77,f68,f60,f56,f93])).

fof(f56,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f60,plain,
    ( spl6_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f76,f61])).

fof(f61,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f76,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f74,f57])).

fof(f57,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f91,plain,
    ( ~ spl6_10
    | ~ spl6_7
    | spl6_9 ),
    inference(avatar_split_clause,[],[f86,f83,f68,f89])).

fof(f83,plain,
    ( spl6_9
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f86,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_7
    | spl6_9 ),
    inference(forward_demodulation,[],[f84,f75])).

fof(f75,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl6_7 ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f84,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f22,f83])).

fof(f22,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

fof(f81,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f72,f68,f79])).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_7 ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (15007)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.45  % (15007)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % (15022)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f81,f85,f91,f95,f99,f104,f114])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_8 | spl6_10 | ~spl6_13),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_8 | spl6_10 | ~spl6_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f112,f90])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl6_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f89])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    spl6_10 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_8 | ~spl6_13)),
% 0.22/0.45    inference(resolution,[],[f110,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    r2_hidden(sK5,sK2) | ~spl6_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl6_3 <=> r2_hidden(sK5,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_13)),
% 0.22/0.45    inference(forward_demodulation,[],[f109,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    sK4 = k1_funct_1(sK3,sK5) | ~spl6_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl6_6 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK5),k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0)) ) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_13)),
% 0.22/0.45    inference(resolution,[],[f108,f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    r2_hidden(sK5,sK0) | ~spl6_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    spl6_2 <=> r2_hidden(sK5,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1)) | ~r2_hidden(X0,X1)) ) | (~spl6_1 | ~spl6_8 | ~spl6_13)),
% 0.22/0.46    inference(forward_demodulation,[],[f107,f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) ) | ~spl6_8),
% 0.22/0.46    inference(resolution,[],[f80,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    v1_relat_1(sK3) | ~spl6_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl6_8 <=> v1_relat_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1)))) ) | (~spl6_1 | ~spl6_8 | ~spl6_13)),
% 0.22/0.46    inference(subsumption_resolution,[],[f106,f80])).
% 0.22/0.46  fof(f106,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1)))) ) | (~spl6_1 | ~spl6_13)),
% 0.22/0.46    inference(subsumption_resolution,[],[f105,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(k7_relat_1(sK3,X1)))) ) | ~spl6_13),
% 0.22/0.46    inference(superposition,[],[f28,f102])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    sK0 = k1_relat_1(sK3) | ~spl6_13),
% 0.22/0.46    inference(avatar_component_clause,[],[f101])).
% 0.22/0.46  fof(f101,plain,(
% 0.22/0.46    spl6_13 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).
% 0.22/0.46  fof(f104,plain,(
% 0.22/0.46    spl6_13 | ~spl6_11 | ~spl6_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f103,f97,f93,f101])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl6_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    spl6_12 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    sK0 = k1_relat_1(sK3) | (~spl6_11 | ~spl6_12)),
% 0.22/0.46    inference(forward_demodulation,[],[f98,f94])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f93])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f97])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    spl6_12 | ~spl6_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f71,f68,f97])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_7),
% 0.22/0.46    inference(resolution,[],[f69,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f68])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl6_11 | spl6_4 | ~spl6_5 | ~spl6_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f77,f68,f60,f56,f93])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    spl6_4 <=> k1_xboole_0 = sK1),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    spl6_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl6_4 | ~spl6_5 | ~spl6_7)),
% 0.22/0.46    inference(subsumption_resolution,[],[f76,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl6_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f60])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl6_4 | ~spl6_7)),
% 0.22/0.46    inference(subsumption_resolution,[],[f74,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    k1_xboole_0 != sK1 | spl6_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f56])).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl6_7),
% 0.22/0.46    inference(resolution,[],[f69,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(flattening,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.46  fof(f91,plain,(
% 0.22/0.46    ~spl6_10 | ~spl6_7 | spl6_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f86,f83,f68,f89])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl6_9 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.46  fof(f86,plain,(
% 0.22/0.46    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_7 | spl6_9)),
% 0.22/0.46    inference(forward_demodulation,[],[f84,f75])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl6_7),
% 0.22/0.46    inference(resolution,[],[f69,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl6_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f83])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    ~spl6_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f22,f83])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.46    inference(flattening,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f7])).
% 0.22/0.46  fof(f7,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    spl6_8 | ~spl6_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f72,f68,f79])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    v1_relat_1(sK3) | ~spl6_7),
% 0.22/0.46    inference(resolution,[],[f69,f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    spl6_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f68])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    spl6_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f21,f64])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    sK4 = k1_funct_1(sK3,sK5)),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    spl6_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f24,f60])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ~spl6_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    k1_xboole_0 != sK1),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl6_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f20,f52])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    r2_hidden(sK5,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    spl6_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f19,f48])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    r2_hidden(sK5,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    spl6_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    v1_funct_1(sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (15007)------------------------------
% 0.22/0.46  % (15007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (15007)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (15007)Memory used [KB]: 6140
% 0.22/0.46  % (15007)Time elapsed: 0.049 s
% 0.22/0.46  % (15007)------------------------------
% 0.22/0.46  % (15007)------------------------------
% 0.22/0.46  % (15006)Success in time 0.095 s
%------------------------------------------------------------------------------
