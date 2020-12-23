%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1016+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 479 expanded)
%              Number of leaves         :   16 ( 133 expanded)
%              Depth                    :   26
%              Number of atoms          :  471 (3984 expanded)
%              Number of equality atoms :  113 (1184 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f68,f81,f85,f111,f136,f138])).

fof(f138,plain,
    ( spl6_6
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f137,f74,f42,f66])).

fof(f66,plain,
    ( spl6_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f42,plain,
    ( spl6_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f74,plain,
    ( spl6_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f137,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X1)
        | X1 = X2 )
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f43,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f128,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X1)
        | ~ v2_funct_1(sK1)
        | X1 = X2 )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f127,f88])).

fof(f88,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f83,f87])).

fof(f87,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f26,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

% (8577)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f17,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f86,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(sK1,X0,X0)
      | k1_relset_1(X0,X0,sK1) = X0 ) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f127,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | X1 = X2 )
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f126,f88])).

fof(f126,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | X1 = X2 )
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f70,f75])).

fof(f75,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f70,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X1)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | X1 = X2
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | X3 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f136,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f134,f48])).

fof(f48,plain,
    ( sK2 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f134,plain,
    ( sK2 = sK3
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( sK2 = sK3
    | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK2)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f130,f63])).

fof(f63,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK3 = X0
        | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f129,f53])).

fof(f53,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f129,plain,
    ( ! [X0] :
        ( sK3 = X0
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,sK3) != k1_funct_1(sK1,X0) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | X4 = X5
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f58,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f111,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f109,f75])).

fof(f109,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f108,f25])).

fof(f108,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f107,f44])).

fof(f44,plain,
    ( ~ v2_funct_1(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f107,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(superposition,[],[f37,f102])).

fof(f102,plain,
    ( sK4(sK1) = sK5(sK1)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f101,f80])).

fof(f80,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_8
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f101,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f97,f96])).

fof(f96,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f95,f75])).

fof(f95,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f94,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f88])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK4(sK1) = X0
        | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) )
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f93,f67])).

fof(f93,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f92,f75])).

fof(f92,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f89,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f34,f88])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f82,f27])).

fof(f82,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_7 ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f76,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f81,plain,
    ( ~ spl6_7
    | spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f72,f42,f78,f74])).

fof(f72,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f71,f25])).

fof(f71,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f28,f66,f42])).

fof(f28,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f29,f61,f42])).

fof(f29,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f30,f56,f42])).

fof(f30,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f31,f51,f42])).

fof(f31,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f32,f46,f42])).

fof(f32,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
