%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 529 expanded)
%              Number of leaves         :   14 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          :  542 (4079 expanded)
%              Number of equality atoms :  118 (1206 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f99,f131,f157,f160,f172])).

fof(f172,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f170,f163])).

fof(f163,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f53,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f53,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_4
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f170,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f166,f164])).

fof(f164,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f58,f74])).

fof(f58,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_5
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f166,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ sP0(sK2,X0)
        | ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK4,X0) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f43,plain,
    ( sK3 != sK4
    | spl7_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_2
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f152,plain,
    ( ! [X0] :
        ( sK3 = sK4
        | ~ r2_hidden(sK4,X0)
        | ~ r2_hidden(sK3,X0)
        | ~ sP0(sK2,X0) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(X0,X1)
        | ~ sP0(sK2,X1) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f38,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl7_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(X0,X1)
        | ~ v2_funct_1(sK2)
        | ~ sP0(sK2,X1) )
    | ~ spl7_3 ),
    inference(superposition,[],[f28,f48])).

fof(f48,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl7_3
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
      | X4 = X5
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ( sK5(X0,X1) != sK6(X0,X1)
            & k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1))
            & r2_hidden(sK6(X0,X1),X1)
            & r2_hidden(sK5(X0,X1),X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) ) )
      | ~ sP0(X2,X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X2,X0] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ~ sP0(X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f107,plain,
    ( sP0(sK2,k1_xboole_0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f106,f20])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK3 != sK4
        & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
        & r2_hidden(sK4,sK1)
        & r2_hidden(sK3,sK1) )
      | ~ v2_funct_1(sK2) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
          | ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(X4,sK1) )
      | v2_funct_1(sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f14,f13])).

fof(f13,plain,
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
            & k1_funct_1(sK2,X2) = k1_funct_1(sK2,X3)
            & r2_hidden(X3,sK1)
            & r2_hidden(X2,sK1) )
        | ~ v2_funct_1(sK2) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
            | ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(X4,sK1) )
        | v2_funct_1(sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK2,X2) = k1_funct_1(sK2,X3)
        & r2_hidden(X3,sK1)
        & r2_hidden(X2,sK1) )
   => ( sK3 != sK4
      & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
      & r2_hidden(sK4,sK1)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
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
    inference(flattening,[],[f4])).

fof(f4,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f106,plain,
    ( sP0(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f104,f100])).

fof(f100,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f21,f74])).

fof(f21,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,
    ( sP0(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | sP0(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f7,f8])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f22,f74])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f160,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f159,f72,f68])).

fof(f68,plain,
    ( spl7_7
  <=> sP0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | sP0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f158,f20])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | sP0(sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f21])).

fof(f135,plain,
    ( k1_xboole_0 = sK1
    | sP0(sK2,sK1)
    | ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | sP0(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f157,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f155,f53])).

fof(f155,plain,
    ( ~ r2_hidden(sK4,sK1)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f154,f58])).

fof(f154,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK4,sK1)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(resolution,[],[f153,f70])).

fof(f70,plain,
    ( sP0(sK2,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f131,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f129,f107])).

fof(f129,plain,
    ( ~ sP0(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f128,f39])).

fof(f39,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f128,plain,
    ( v2_funct_1(sK2)
    | ~ sP0(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( sK5(sK2,k1_xboole_0) != sK5(sK2,k1_xboole_0)
    | v2_funct_1(sK2)
    | ~ sP0(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f32,f124])).

fof(f124,plain,
    ( sK5(sK2,k1_xboole_0) = sK6(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f123,f111])).

fof(f111,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f108,f39])).

fof(f108,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | sK5(sK2,k1_xboole_0) = sK6(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0))
        | ~ r2_hidden(X0,k1_xboole_0)
        | sK6(sK2,k1_xboole_0) = X0 )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f116,f112])).

fof(f112,plain,
    ( r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0)
    | spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f109,plain,
    ( r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0))
        | ~ r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | sK6(sK2,k1_xboole_0) = X0 )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f103,f113])).

fof(f113,plain,
    ( k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) = k1_funct_1(sK2,sK6(sK2,k1_xboole_0))
    | spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f110,f39])).

fof(f110,plain,
    ( k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) = k1_funct_1(sK2,sK6(sK2,k1_xboole_0))
    | v2_funct_1(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
        | ~ r2_hidden(X5,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0)
        | X4 = X5 )
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f102,f74])).

fof(f102,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
        | ~ r2_hidden(X4,sK1)
        | X4 = X5 )
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f62,f74])).

fof(f62,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | X4 = X5 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != sK6(X0,X1)
      | v2_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f97,f70])).

fof(f97,plain,
    ( ~ sP0(sK2,sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,
    ( v2_funct_1(sK2)
    | ~ sP0(sK2,sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( sK5(sK2,sK1) != sK5(sK2,sK1)
    | v2_funct_1(sK2)
    | ~ sP0(sK2,sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f32,f92])).

fof(f92,plain,
    ( sK5(sK2,sK1) = sK6(sK2,sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f91,f79])).

fof(f79,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f76,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | v2_funct_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f70,f29])).

fof(f91,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK5(sK2,sK1) = sK6(sK2,sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,sK1))
        | ~ r2_hidden(X0,sK1)
        | sK6(sK2,sK1) = X0 )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f84,f80])).

fof(f80,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | v2_funct_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f70,f30])).

fof(f84,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK6(sK2,sK1),sK1)
        | sK6(sK2,sK1) = X0 )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f62,f81])).

fof(f81,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = k1_funct_1(sK2,sK6(sK2,sK1))
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f78,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK1)) = k1_funct_1(sK2,sK6(sK2,sK1))
    | v2_funct_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f70,f31])).

fof(f63,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f23,f61,f37])).

fof(f23,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1)
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f24,f56,f37])).

fof(f24,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f25,f51,f37])).

fof(f25,plain,
    ( r2_hidden(sK4,sK1)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f26,f46,f37])).

fof(f26,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f27,f41,f37])).

fof(f27,plain,
    ( sK3 != sK4
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (15172)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (15174)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (15194)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (15191)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (15172)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f99,f131,f157,f160,f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f170,f163])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    r2_hidden(sK4,k1_xboole_0) | (~spl7_4 | ~spl7_8)),
% 0.22/0.50    inference(backward_demodulation,[],[f53,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl7_8 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    r2_hidden(sK4,sK1) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl7_4 <=> r2_hidden(sK4,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k1_xboole_0) | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f166,f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_xboole_0) | (~spl7_5 | ~spl7_8)),
% 0.22/0.50    inference(backward_demodulation,[],[f58,f74])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    r2_hidden(sK3,sK1) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl7_5 <=> r2_hidden(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(sK4,k1_xboole_0) | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_8)),
% 0.22/0.50    inference(resolution,[],[f107,f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (~sP0(sK2,X0) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK4,X0)) ) | (~spl7_1 | spl7_2 | ~spl7_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f152,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    sK3 != sK4 | spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl7_2 <=> sK3 = sK4),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X0] : (sK3 = sK4 | ~r2_hidden(sK4,X0) | ~r2_hidden(sK3,X0) | ~sP0(sK2,X0)) ) | (~spl7_1 | ~spl7_3)),
% 0.22/0.50    inference(equality_resolution,[],[f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,X1) | ~r2_hidden(X0,X1) | ~sP0(sK2,X1)) ) | (~spl7_1 | ~spl7_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    spl7_1 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,X1) | ~r2_hidden(X0,X1) | ~v2_funct_1(sK2) | ~sP0(sK2,X1)) ) | ~spl7_3),
% 0.22/0.50    inference(superposition,[],[f28,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl7_3 <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X4,X0,X5,X1] : (k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~v2_funct_1(X0) | ~sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (((v2_funct_1(X0) | (sK5(X0,X1) != sK6(X0,X1) & k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK5(X0,X1) != sK6(X0,X1) & k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (((v2_funct_1(X0) | ? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 0.22/0.50    inference(rectify,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X2,X0] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_funct_1(X2))) | ~sP0(X2,X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X2,X0] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | ~sP0(X2,X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    sP0(sK2,k1_xboole_0) | ~spl7_8),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ((sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK1) & r2_hidden(sK3,sK1)) | ~v2_funct_1(sK2)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) | v2_funct_1(sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f14,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK2,X2) = k1_funct_1(sK2,X3) & r2_hidden(X3,sK1) & r2_hidden(X2,sK1)) | ~v2_funct_1(sK2)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) | v2_funct_1(sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK2,X2) = k1_funct_1(sK2,X3) & r2_hidden(X3,sK1) & r2_hidden(X2,sK1)) => (sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK1) & r2_hidden(sK3,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.50    inference(rectify,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.50    inference(flattening,[],[f4])).
% 0.22/0.50  fof(f4,plain,(
% 0.22/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.50    inference(negated_conjecture,[],[f2])).
% 0.22/0.50  fof(f2,conjecture,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    sP0(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl7_8),
% 0.22/0.50    inference(subsumption_resolution,[],[f104,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl7_8),
% 0.22/0.50    inference(backward_demodulation,[],[f21,f74])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK1,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    sP0(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f101,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | sP0(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sP0(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (sP0(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(definition_folding,[],[f7,f8])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_8),
% 0.22/0.50    inference(backward_demodulation,[],[f22,f74])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl7_7 | spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f72,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl7_7 <=> sP0(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sP0(sK2,sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f158,f20])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sP0(sK2,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f135,f21])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sP0(sK2,sK1) | ~v1_funct_2(sK2,sK1,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f22,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | sP0(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f155,f53])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ~r2_hidden(sK4,sK1) | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f154,f58])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ~r2_hidden(sK3,sK1) | ~r2_hidden(sK4,sK1) | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_7)),
% 0.22/0.50    inference(resolution,[],[f153,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    sP0(sK2,sK1) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl7_1 | ~spl7_6 | ~spl7_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f129,f107])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ~sP0(sK2,k1_xboole_0) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f128,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~sP0(sK2,k1_xboole_0) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    sK5(sK2,k1_xboole_0) != sK5(sK2,k1_xboole_0) | v2_funct_1(sK2) | ~sP0(sK2,k1_xboole_0) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(superposition,[],[f32,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    sK5(sK2,k1_xboole_0) = sK6(sK2,k1_xboole_0) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) | (spl7_1 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f108,f39])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) | v2_funct_1(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f107,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | r2_hidden(sK5(X0,X1),X1) | v2_funct_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) | sK5(sK2,k1_xboole_0) = sK6(sK2,k1_xboole_0) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(equality_resolution,[],[f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) | ~r2_hidden(X0,k1_xboole_0) | sK6(sK2,k1_xboole_0) = X0) ) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0) | (spl7_1 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f109,f39])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0) | v2_funct_1(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f107,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | r2_hidden(sK6(X0,X1),X1) | v2_funct_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) | ~r2_hidden(sK6(sK2,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | sK6(sK2,k1_xboole_0) = X0) ) | (spl7_1 | ~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(superposition,[],[f103,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) = k1_funct_1(sK2,sK6(sK2,k1_xboole_0)) | (spl7_1 | ~spl7_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f39])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) = k1_funct_1(sK2,sK6(sK2,k1_xboole_0)) | v2_funct_1(sK2) | ~spl7_8),
% 0.22/0.50    inference(resolution,[],[f107,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | k1_funct_1(X0,sK5(X0,X1)) = k1_funct_1(X0,sK6(X0,X1)) | v2_funct_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X4,X5] : (k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0) | X4 = X5) ) | (~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(forward_demodulation,[],[f102,f74])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X4,sK1) | X4 = X5) ) | (~spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(backward_demodulation,[],[f62,f74])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X4,X5] : (k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK1) | X4 = X5) ) | ~spl7_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK1) | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK5(X0,X1) != sK6(X0,X1) | v2_funct_1(X0) | ~sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl7_1 | ~spl7_6 | ~spl7_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f97,f70])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~sP0(sK2,sK1) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f39])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~sP0(sK2,sK1) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    sK5(sK2,sK1) != sK5(sK2,sK1) | v2_funct_1(sK2) | ~sP0(sK2,sK1) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(superposition,[],[f32,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    sK5(sK2,sK1) = sK6(sK2,sK1) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2,sK1),sK1) | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f39])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2,sK1),sK1) | v2_funct_1(sK2) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f70,f29])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK2,sK1),sK1) | sK5(sK2,sK1) = sK6(sK2,sK1) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(equality_resolution,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,sK1)) | ~r2_hidden(X0,sK1) | sK6(sK2,sK1) = X0) ) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    r2_hidden(sK6(sK2,sK1),sK1) | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f39])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    r2_hidden(sK6(sK2,sK1),sK1) | v2_funct_1(sK2) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f70,f30])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0] : (k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2,sK1)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK6(sK2,sK1),sK1) | sK6(sK2,sK1) = X0) ) | (spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.22/0.50    inference(superposition,[],[f62,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,sK1)) = k1_funct_1(sK2,sK6(sK2,sK1)) | (spl7_1 | ~spl7_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f39])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK5(sK2,sK1)) = k1_funct_1(sK2,sK6(sK2,sK1)) | v2_funct_1(sK2) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f70,f31])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl7_1 | spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f61,f37])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK2,X4) != k1_funct_1(sK2,X5) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1) | v2_funct_1(sK2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~spl7_1 | spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f56,f37])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    r2_hidden(sK3,sK1) | ~v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~spl7_1 | spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f51,f37])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r2_hidden(sK4,sK1) | ~v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~spl7_1 | spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f46,f37])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~spl7_1 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f41,f37])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    sK3 != sK4 | ~v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15172)------------------------------
% 0.22/0.50  % (15172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15172)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15172)Memory used [KB]: 10618
% 0.22/0.50  % (15172)Time elapsed: 0.095 s
% 0.22/0.50  % (15172)------------------------------
% 0.22/0.50  % (15172)------------------------------
% 0.22/0.50  % (15189)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (15186)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (15170)Success in time 0.146 s
%------------------------------------------------------------------------------
