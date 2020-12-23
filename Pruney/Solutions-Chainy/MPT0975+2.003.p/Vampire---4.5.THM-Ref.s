%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:16 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 149 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  268 ( 784 expanded)
%              Number of equality atoms :   69 ( 203 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f74,f81,f89,f98,f104,f107,f113])).

fof(f113,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f109,f96,f56,f52,f60,f44])).

fof(f44,plain,
    ( spl5_1
  <=> k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f60,plain,
    ( spl5_5
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f52,plain,
    ( spl5_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f56,plain,
    ( spl5_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f96,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f109,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f108,f57])).

fof(f57,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k5_relat_1(sK3,X0),sK2) = k1_funct_1(X0,k1_funct_1(sK3,sK2)) )
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f107,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f103,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_13
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f104,plain,
    ( ~ spl5_13
    | ~ spl5_6
    | spl5_11 ),
    inference(avatar_split_clause,[],[f100,f92,f64,f102])).

fof(f64,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f92,plain,
    ( spl5_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_6
    | spl5_11 ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_11 ),
    inference(resolution,[],[f93,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,
    ( ~ spl5_11
    | ~ spl5_8
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f90,f86,f96,f72,f92])).

fof(f72,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f86,plain,
    ( spl5_10
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_10 ),
    inference(superposition,[],[f30,f87])).

fof(f87,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f89,plain,
    ( ~ spl5_6
    | spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f83,f77,f86,f64])).

fof(f77,plain,
    ( spl5_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f83,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(superposition,[],[f31,f78])).

% (9079)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f78,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f81,plain,
    ( spl5_9
    | spl5_2
    | ~ spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f75,f64,f68,f48,f77])).

fof(f48,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f68,plain,
    ( spl5_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f75,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f32,f65])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f74,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f20,f72])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
            & k1_xboole_0 != X1
            & r2_hidden(X2,X0)
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2))
          & k1_xboole_0 != sK1
          & r2_hidden(sK2,sK0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X4] :
        ( k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2))
        & k1_xboole_0 != sK1
        & r2_hidden(sK2,sK0)
        & v1_funct_1(X4)
        & v1_relat_1(X4) )
   => ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_relat_1(X4) )
           => ( r2_hidden(X2,X0)
             => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
                | k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

fof(f70,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f21,f68])).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f27,f44])).

fof(f27,plain,(
    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:27:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.43  % (9077)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.44  % (9078)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.44  % (9087)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.44  % (9072)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.44  % (9078)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f118,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f74,f81,f89,f98,f104,f107,f113])).
% 0.18/0.44  fof(f113,plain,(
% 0.18/0.44    spl5_1 | ~spl5_5 | ~spl5_3 | ~spl5_4 | ~spl5_12),
% 0.18/0.44    inference(avatar_split_clause,[],[f109,f96,f56,f52,f60,f44])).
% 0.18/0.44  fof(f44,plain,(
% 0.18/0.44    spl5_1 <=> k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.44  fof(f60,plain,(
% 0.18/0.44    spl5_5 <=> v1_relat_1(sK4)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.18/0.44  fof(f52,plain,(
% 0.18/0.44    spl5_3 <=> r2_hidden(sK2,sK0)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.18/0.44  fof(f56,plain,(
% 0.18/0.44    spl5_4 <=> v1_funct_1(sK4)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.18/0.44  fof(f96,plain,(
% 0.18/0.44    spl5_12 <=> ! [X1,X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.18/0.44  fof(f109,plain,(
% 0.18/0.44    ~v1_relat_1(sK4) | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) | (~spl5_3 | ~spl5_4 | ~spl5_12)),
% 0.18/0.44    inference(resolution,[],[f108,f57])).
% 0.18/0.44  fof(f57,plain,(
% 0.18/0.44    v1_funct_1(sK4) | ~spl5_4),
% 0.18/0.44    inference(avatar_component_clause,[],[f56])).
% 0.18/0.44  fof(f108,plain,(
% 0.18/0.44    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k5_relat_1(sK3,X0),sK2) = k1_funct_1(X0,k1_funct_1(sK3,sK2))) ) | (~spl5_3 | ~spl5_12)),
% 0.18/0.44    inference(resolution,[],[f97,f53])).
% 0.18/0.44  fof(f53,plain,(
% 0.18/0.44    r2_hidden(sK2,sK0) | ~spl5_3),
% 0.18/0.44    inference(avatar_component_clause,[],[f52])).
% 0.18/0.44  fof(f97,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))) ) | ~spl5_12),
% 0.18/0.44    inference(avatar_component_clause,[],[f96])).
% 0.18/0.44  fof(f107,plain,(
% 0.18/0.44    spl5_13),
% 0.18/0.44    inference(avatar_contradiction_clause,[],[f105])).
% 0.18/0.44  fof(f105,plain,(
% 0.18/0.44    $false | spl5_13),
% 0.18/0.44    inference(resolution,[],[f103,f29])).
% 0.18/0.44  fof(f29,plain,(
% 0.18/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f2])).
% 0.18/0.44  fof(f2,axiom,(
% 0.18/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.44  fof(f103,plain,(
% 0.18/0.44    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_13),
% 0.18/0.44    inference(avatar_component_clause,[],[f102])).
% 0.18/0.44  fof(f102,plain,(
% 0.18/0.44    spl5_13 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.18/0.44  fof(f104,plain,(
% 0.18/0.44    ~spl5_13 | ~spl5_6 | spl5_11),
% 0.18/0.44    inference(avatar_split_clause,[],[f100,f92,f64,f102])).
% 0.18/0.44  fof(f64,plain,(
% 0.18/0.44    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.18/0.44  fof(f92,plain,(
% 0.18/0.44    spl5_11 <=> v1_relat_1(sK3)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.18/0.44  fof(f100,plain,(
% 0.18/0.44    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_6 | spl5_11)),
% 0.18/0.44    inference(resolution,[],[f99,f65])).
% 0.18/0.44  fof(f65,plain,(
% 0.18/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 0.18/0.44    inference(avatar_component_clause,[],[f64])).
% 0.18/0.44  fof(f99,plain,(
% 0.18/0.44    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_11),
% 0.18/0.44    inference(resolution,[],[f93,f28])).
% 0.18/0.44  fof(f28,plain,(
% 0.18/0.44    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.44  fof(f93,plain,(
% 0.18/0.44    ~v1_relat_1(sK3) | spl5_11),
% 0.18/0.44    inference(avatar_component_clause,[],[f92])).
% 0.18/0.44  fof(f98,plain,(
% 0.18/0.44    ~spl5_11 | ~spl5_8 | spl5_12 | ~spl5_10),
% 0.18/0.44    inference(avatar_split_clause,[],[f90,f86,f96,f72,f92])).
% 0.18/0.44  fof(f72,plain,(
% 0.18/0.44    spl5_8 <=> v1_funct_1(sK3)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.18/0.44  fof(f86,plain,(
% 0.18/0.44    spl5_10 <=> sK0 = k1_relat_1(sK3)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.18/0.44  fof(f90,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_10),
% 0.18/0.44    inference(superposition,[],[f30,f87])).
% 0.18/0.44  fof(f87,plain,(
% 0.18/0.44    sK0 = k1_relat_1(sK3) | ~spl5_10),
% 0.18/0.44    inference(avatar_component_clause,[],[f86])).
% 0.18/0.44  fof(f30,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f12])).
% 0.18/0.44  fof(f12,plain,(
% 0.18/0.44    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.18/0.44    inference(flattening,[],[f11])).
% 0.18/0.44  fof(f11,plain,(
% 0.18/0.44    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.18/0.44    inference(ennf_transformation,[],[f3])).
% 0.18/0.44  fof(f3,axiom,(
% 0.18/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.18/0.44  fof(f89,plain,(
% 0.18/0.44    ~spl5_6 | spl5_10 | ~spl5_9),
% 0.18/0.44    inference(avatar_split_clause,[],[f83,f77,f86,f64])).
% 0.18/0.44  fof(f77,plain,(
% 0.18/0.44    spl5_9 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.18/0.44  fof(f83,plain,(
% 0.18/0.44    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.18/0.44    inference(superposition,[],[f31,f78])).
% 0.18/0.44  % (9079)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.44  fof(f78,plain,(
% 0.18/0.44    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_9),
% 0.18/0.44    inference(avatar_component_clause,[],[f77])).
% 0.18/0.44  fof(f31,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f13])).
% 0.18/0.44  fof(f13,plain,(
% 0.18/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.44    inference(ennf_transformation,[],[f4])).
% 0.18/0.44  fof(f4,axiom,(
% 0.18/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.44  fof(f81,plain,(
% 0.18/0.44    spl5_9 | spl5_2 | ~spl5_7 | ~spl5_6),
% 0.18/0.44    inference(avatar_split_clause,[],[f75,f64,f68,f48,f77])).
% 0.18/0.44  fof(f48,plain,(
% 0.18/0.44    spl5_2 <=> k1_xboole_0 = sK1),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.44  fof(f68,plain,(
% 0.18/0.44    spl5_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.18/0.44  fof(f75,plain,(
% 0.18/0.44    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_6),
% 0.18/0.44    inference(resolution,[],[f32,f65])).
% 0.18/0.44  fof(f32,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.18/0.44    inference(cnf_transformation,[],[f19])).
% 0.18/0.44  fof(f19,plain,(
% 0.18/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.44    inference(nnf_transformation,[],[f15])).
% 0.18/0.44  fof(f15,plain,(
% 0.18/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.44    inference(flattening,[],[f14])).
% 0.18/0.44  fof(f14,plain,(
% 0.18/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.44    inference(ennf_transformation,[],[f5])).
% 0.18/0.44  fof(f5,axiom,(
% 0.18/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.44  fof(f74,plain,(
% 0.18/0.44    spl5_8),
% 0.18/0.44    inference(avatar_split_clause,[],[f20,f72])).
% 0.18/0.44  fof(f20,plain,(
% 0.18/0.44    v1_funct_1(sK3)),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f18,plain,(
% 0.18/0.44    (k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(sK4) & v1_relat_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f17,f16])).
% 0.18/0.44  fof(f16,plain,(
% 0.18/0.44    ? [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f17,plain,(
% 0.18/0.44    ? [X4] : (k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(X4) & v1_relat_1(X4)) => (k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f9,plain,(
% 0.18/0.44    ? [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.18/0.44    inference(flattening,[],[f8])).
% 0.18/0.44  fof(f8,plain,(
% 0.18/0.44    ? [X0,X1,X2,X3] : (? [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (v1_funct_1(X4) & v1_relat_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.18/0.44    inference(ennf_transformation,[],[f7])).
% 0.18/0.44  fof(f7,negated_conjecture,(
% 0.18/0.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.18/0.44    inference(negated_conjecture,[],[f6])).
% 0.18/0.44  fof(f6,conjecture,(
% 0.18/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).
% 0.18/0.44  fof(f70,plain,(
% 0.18/0.44    spl5_7),
% 0.18/0.44    inference(avatar_split_clause,[],[f21,f68])).
% 0.18/0.44  fof(f21,plain,(
% 0.18/0.44    v1_funct_2(sK3,sK0,sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f66,plain,(
% 0.18/0.44    spl5_6),
% 0.18/0.44    inference(avatar_split_clause,[],[f22,f64])).
% 0.18/0.44  fof(f22,plain,(
% 0.18/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f62,plain,(
% 0.18/0.44    spl5_5),
% 0.18/0.44    inference(avatar_split_clause,[],[f23,f60])).
% 0.18/0.44  fof(f23,plain,(
% 0.18/0.44    v1_relat_1(sK4)),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f58,plain,(
% 0.18/0.44    spl5_4),
% 0.18/0.44    inference(avatar_split_clause,[],[f24,f56])).
% 0.18/0.44  fof(f24,plain,(
% 0.18/0.44    v1_funct_1(sK4)),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f54,plain,(
% 0.18/0.44    spl5_3),
% 0.18/0.44    inference(avatar_split_clause,[],[f25,f52])).
% 0.18/0.44  fof(f25,plain,(
% 0.18/0.44    r2_hidden(sK2,sK0)),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f50,plain,(
% 0.18/0.44    ~spl5_2),
% 0.18/0.44    inference(avatar_split_clause,[],[f26,f48])).
% 0.18/0.44  fof(f26,plain,(
% 0.18/0.44    k1_xboole_0 != sK1),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  fof(f46,plain,(
% 0.18/0.44    ~spl5_1),
% 0.18/0.44    inference(avatar_split_clause,[],[f27,f44])).
% 0.18/0.44  fof(f27,plain,(
% 0.18/0.44    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.18/0.44    inference(cnf_transformation,[],[f18])).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (9078)------------------------------
% 0.18/0.44  % (9078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (9078)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (9078)Memory used [KB]: 10618
% 0.18/0.44  % (9078)Time elapsed: 0.054 s
% 0.18/0.44  % (9078)------------------------------
% 0.18/0.44  % (9078)------------------------------
% 0.18/0.45  % (9070)Success in time 0.115 s
%------------------------------------------------------------------------------
