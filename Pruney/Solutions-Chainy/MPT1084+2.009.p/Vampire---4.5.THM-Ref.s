%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 222 expanded)
%              Number of leaves         :   30 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  543 (1020 expanded)
%              Number of equality atoms :  126 ( 216 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f109,f128,f162,f174,f188,f189,f230,f231,f242,f255])).

fof(f255,plain,
    ( spl3_5
    | ~ spl3_20
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl3_5
    | ~ spl3_20
    | spl3_21 ),
    inference(subsumption_resolution,[],[f253,f97])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f253,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_20
    | spl3_21 ),
    inference(subsumption_resolution,[],[f251,f241])).

fof(f241,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_21
  <=> m1_subset_1(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f251,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_20 ),
    inference(resolution,[],[f229,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f229,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl3_20
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f242,plain,
    ( spl3_18
    | ~ spl3_21
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f237,f183,f125,f95,f90,f85,f80,f239,f216])).

fof(f216,plain,
    ( spl3_18
  <=> sK1 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f80,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( spl3_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f125,plain,
    ( spl3_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f183,plain,
    ( spl3_17
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f236,f185])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f236,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f235,f185])).

fof(f235,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f234,f127])).

fof(f127,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f234,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f233,f92])).

fof(f92,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f233,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(superposition,[],[f69,f201])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f200,f97])).

fof(f200,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f199,f92])).

fof(f199,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f198,f87])).

fof(f87,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f198,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f197,f82])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f197,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(superposition,[],[f45,f40])).

fof(f40,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
        & ! [X2] :
            ( k3_funct_2(sK0,sK0,X1,X2) = X2
            | ~ m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
      & ! [X2] :
          ( k3_funct_2(sK0,sK0,sK1,X2) = X2
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f69,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f231,plain,
    ( sK1 != k6_relat_1(sK0)
    | r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))
    | ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f230,plain,
    ( spl3_18
    | spl3_20
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f225,f183,f125,f90,f227,f216])).

fof(f225,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f224,f127])).

fof(f224,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f212,f92])).

fof(f212,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f70,f185])).

fof(f70,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f189,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f188,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f187,f167,f80,f183])).

fof(f167,plain,
    ( spl3_15
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f179,f82])).

fof(f179,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_15 ),
    inference(superposition,[],[f52,f169])).

fof(f169,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f174,plain,
    ( spl3_15
    | spl3_16
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f165,f85,f80,f171,f167])).

fof(f171,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f165,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f163,f87])).

fof(f163,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f82])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f162,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f157,f90,f85,f80,f159])).

fof(f159,plain,
    ( spl3_14
  <=> r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f157,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f156,f92])).

fof(f156,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f154,f87])).

fof(f154,plain,
    ( r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f82])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f128,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f122,f80,f125])).

fof(f122,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f82])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f109,plain,
    ( ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f104,f75,f106])).

fof(f106,plain,
    ( spl3_7
  <=> r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( spl3_1
  <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))
    | spl3_1 ),
    inference(backward_demodulation,[],[f77,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f77,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f103,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f62,f100])).

fof(f100,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f36,f95])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f80])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (2899)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.50  % (2878)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (2899)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (2903)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.51  % (2904)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f109,f128,f162,f174,f188,f189,f230,f231,f242,f255])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    spl3_5 | ~spl3_20 | spl3_21),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f254])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    $false | (spl3_5 | ~spl3_20 | spl3_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f253,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl3_5 <=> v1_xboole_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    v1_xboole_0(sK0) | (~spl3_20 | spl3_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f251,f241])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0,sK1),sK0) | spl3_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f239])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    spl3_21 <=> m1_subset_1(sK2(sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK0,sK1),sK0) | v1_xboole_0(sK0) | ~spl3_20),
% 0.22/0.51    inference(resolution,[],[f229,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0,sK1),sK0) | ~spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f227])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    spl3_20 <=> r2_hidden(sK2(sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    spl3_18 | ~spl3_21 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_10 | ~spl3_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f237,f183,f125,f95,f90,f85,f80,f239,f216])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    spl3_18 <=> sK1 = k6_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl3_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl3_4 <=> v1_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl3_10 <=> v1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl3_17 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f236,f185])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK1) | ~spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f183])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f235,f185])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    sK1 = k6_relat_1(k1_relat_1(sK1)) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f234,f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    v1_relat_1(sK1) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    sK1 = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f233,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v1_funct_1(sK1) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    sK1 = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f232])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5)),
% 0.22/0.51    inference(superposition,[],[f69,f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f97])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f199,f92])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) ) | (~spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f198,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    v1_funct_2(sK1,sK0,sK0) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) ) | ~spl3_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f197,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.51    inference(superposition,[],[f45,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(rectify,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    sK1 != k6_relat_1(sK0) | r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) | ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    spl3_18 | spl3_20 | ~spl3_4 | ~spl3_10 | ~spl3_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f225,f183,f125,f90,f227,f216])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | (~spl3_4 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f224,f127])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | ~v1_relat_1(sK1) | (~spl3_4 | ~spl3_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f212,f92])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_17),
% 0.22/0.51    inference(superposition,[],[f70,f185])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    spl3_17 | ~spl3_2 | ~spl3_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f187,f167,f80,f183])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl3_15 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK1) | (~spl3_2 | ~spl3_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f179,f82])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_15),
% 0.22/0.51    inference(superposition,[],[f52,f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    spl3_15 | spl3_16 | ~spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f165,f85,f80,f171,f167])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    spl3_16 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f87])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f46,f82])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    spl3_14 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f157,f90,f85,f80,f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    spl3_14 <=> r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    r2_funct_2(sK0,sK0,sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f92])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f87])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f73,f82])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.51    inference(equality_resolution,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl3_10 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f122,f80,f125])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    v1_relat_1(sK1) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f57,f82])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~spl3_7 | spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f104,f75,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl3_7 <=> r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl3_1 <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) | spl3_1),
% 0.22/0.51    inference(backward_demodulation,[],[f77,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl3_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f95])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f90])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f85])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f80])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f75])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (2899)------------------------------
% 0.22/0.51  % (2899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2899)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (2899)Memory used [KB]: 6396
% 0.22/0.51  % (2899)Time elapsed: 0.104 s
% 0.22/0.51  % (2899)------------------------------
% 0.22/0.51  % (2899)------------------------------
% 0.22/0.52  % (2877)Success in time 0.149 s
%------------------------------------------------------------------------------
