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
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 466 expanded)
%              Number of leaves         :   28 ( 140 expanded)
%              Depth                    :   26
%              Number of atoms          :  645 (3329 expanded)
%              Number of equality atoms :  136 ( 944 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14287)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f94,f104,f112,f139,f178,f235,f258,f300,f320,f339,f369])).

fof(f369,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f367,f74])).

fof(f74,plain,
    ( sK2 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f367,plain,
    ( sK2 = sK3
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f366,f304])).

fof(f304,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f89,f234])).

fof(f234,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f89,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f366,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | sK2 = sK3
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_23 ),
    inference(equality_resolution,[],[f340])).

fof(f340,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
        | ~ r2_hidden(X2,k1_xboole_0)
        | sK3 = X2 )
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f253,f321])).

fof(f321,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f138,f234])).

fof(f138,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_12
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f253,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | sK3 = X2 )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_23
  <=> ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | sK3 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f339,plain,
    ( ~ spl7_4
    | ~ spl7_12
    | ~ spl7_21
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_21
    | spl7_22 ),
    inference(subsumption_resolution,[],[f334,f303])).

fof(f303,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f84,f234])).

fof(f84,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f334,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_21
    | spl7_22 ),
    inference(backward_demodulation,[],[f250,f321])).

fof(f250,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_22
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f320,plain,
    ( spl7_11
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl7_11
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f314,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f314,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | spl7_11
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f134,f234])).

fof(f134,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_11
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f300,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_20 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_20 ),
    inference(subsumption_resolution,[],[f296,f74])).

fof(f296,plain,
    ( sK2 = sK3
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_20 ),
    inference(backward_demodulation,[],[f265,f289])).

fof(f289,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_5
    | spl7_20 ),
    inference(resolution,[],[f237,f230])).

fof(f230,plain,
    ( ~ sP6(sK1,sK0)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_20
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f237,plain,
    ( ! [X0] :
        ( sP6(X0,sK0)
        | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) )
    | ~ spl7_5 ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f65_D])).

fof(f65_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f265,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_20 ),
    inference(forward_demodulation,[],[f264,f79])).

fof(f79,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f264,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_4
    | spl7_20 ),
    inference(resolution,[],[f236,f230])).

fof(f236,plain,
    ( ! [X0] :
        ( sP6(X0,sK0)
        | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f84,f65])).

fof(f258,plain,
    ( ~ spl7_22
    | spl7_23
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f257,f97,f77,f68,f252,f248])).

fof(f68,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f97,plain,
    ( spl7_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f257,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2)
        | sK3 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,k1_relat_1(sK1)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f256,f98])).

fof(f98,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f256,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2)
        | sK3 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f255,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f29,f28])).

% (14271)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f28,plain,
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

fof(f29,plain,
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f255,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2)
        | sK3 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f241,f69])).

fof(f69,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f241,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2)
        | sK3 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_3 ),
    inference(superposition,[],[f47,f79])).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f235,plain,
    ( ~ spl7_20
    | spl7_21
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f226,f68,f232,f228])).

fof(f226,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f225,f38])).

fof(f225,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f39,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f62,f65_D])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f178,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f176,f98])).

fof(f176,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f175,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f174,f70])).

fof(f70,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f174,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f51,f167])).

fof(f167,plain,
    ( sK4(sK1) = sK5(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f166,f156])).

fof(f156,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f155,f98])).

fof(f155,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f154,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f150,f70])).

fof(f150,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f129,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f129,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f126,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f126,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f125,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f60,f105])).

fof(f105,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f166,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f158,f153])).

fof(f153,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f152,f98])).

fof(f152,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f151,f38])).

fof(f151,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f149,f70])).

fof(f149,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f129,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f158,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK5(sK1),sK0)
        | sK5(sK1) = X0 )
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f93,f103])).

fof(f103,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_8
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f93,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f51,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f139,plain,
    ( ~ spl7_11
    | spl7_12 ),
    inference(avatar_split_clause,[],[f130,f136,f132])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f128,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f128,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f126,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f106,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f106,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f104,plain,
    ( ~ spl7_7
    | spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f95,f101,f68,f97])).

fof(f95,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f41,f92,f68])).

fof(f41,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f42,f87,f68])).

fof(f42,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f43,f82,f68])).

fof(f43,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f44,f77,f68])).

fof(f44,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f45,f72,f68])).

fof(f45,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (14272)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.45  % (14272)Refutation not found, incomplete strategy% (14272)------------------------------
% 0.20/0.45  % (14272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (14272)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (14272)Memory used [KB]: 10618
% 0.20/0.45  % (14272)Time elapsed: 0.069 s
% 0.20/0.45  % (14272)------------------------------
% 0.20/0.45  % (14272)------------------------------
% 0.20/0.47  % (14280)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (14288)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (14269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (14268)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (14267)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (14274)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (14290)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.49  % (14285)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (14270)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (14267)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (14287)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f94,f104,f112,f139,f178,f235,f258,f300,f320,f339,f369])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    spl7_2 | ~spl7_5 | ~spl7_12 | ~spl7_21 | ~spl7_23),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f368])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    $false | (spl7_2 | ~spl7_5 | ~spl7_12 | ~spl7_21 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f367,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    sK2 != sK3 | spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl7_2 <=> sK2 = sK3),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f367,plain,(
% 0.20/0.49    sK2 = sK3 | (~spl7_5 | ~spl7_12 | ~spl7_21 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f366,f304])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    r2_hidden(sK2,k1_xboole_0) | (~spl7_5 | ~spl7_21)),
% 0.20/0.49    inference(backward_demodulation,[],[f89,f234])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl7_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f232])).
% 0.20/0.49  fof(f232,plain,(
% 0.20/0.49    spl7_21 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl7_5 <=> r2_hidden(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f366,plain,(
% 0.20/0.49    ~r2_hidden(sK2,k1_xboole_0) | sK2 = sK3 | (~spl7_12 | ~spl7_21 | ~spl7_23)),
% 0.20/0.49    inference(equality_resolution,[],[f340])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_xboole_0) | sK3 = X2) ) | (~spl7_12 | ~spl7_21 | ~spl7_23)),
% 0.20/0.49    inference(forward_demodulation,[],[f253,f321])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(sK1) | (~spl7_12 | ~spl7_21)),
% 0.20/0.49    inference(forward_demodulation,[],[f138,f234])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK1) | ~spl7_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl7_12 <=> sK0 = k1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK3 = X2) ) | ~spl7_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f252])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    spl7_23 <=> ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK3 = X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    ~spl7_4 | ~spl7_12 | ~spl7_21 | spl7_22),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f338])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    $false | (~spl7_4 | ~spl7_12 | ~spl7_21 | spl7_22)),
% 0.20/0.49    inference(subsumption_resolution,[],[f334,f303])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    r2_hidden(sK3,k1_xboole_0) | (~spl7_4 | ~spl7_21)),
% 0.20/0.49    inference(backward_demodulation,[],[f84,f234])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    r2_hidden(sK3,sK0) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl7_4 <=> r2_hidden(sK3,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f334,plain,(
% 0.20/0.49    ~r2_hidden(sK3,k1_xboole_0) | (~spl7_12 | ~spl7_21 | spl7_22)),
% 0.20/0.49    inference(backward_demodulation,[],[f250,f321])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    ~r2_hidden(sK3,k1_relat_1(sK1)) | spl7_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f248])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    spl7_22 <=> r2_hidden(sK3,k1_relat_1(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    spl7_11 | ~spl7_21),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f319])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    $false | (spl7_11 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f314,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | (spl7_11 | ~spl7_21)),
% 0.20/0.49    inference(backward_demodulation,[],[f134,f234])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ~r1_tarski(sK0,k1_relat_1(sK1)) | spl7_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl7_11 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    $false | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f296,f74])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    sK2 = sK3 | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_20)),
% 0.20/0.49    inference(backward_demodulation,[],[f265,f289])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_5 | spl7_20)),
% 0.20/0.49    inference(resolution,[],[f237,f230])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    ~sP6(sK1,sK0) | spl7_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    spl7_20 <=> sP6(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    ( ! [X0] : (sP6(X0,sK0) | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f89,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f65_D])).
% 0.20/0.49  fof(f65_D,plain,(
% 0.20/0.49    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.20/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_3 | ~spl7_4 | spl7_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f264,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl7_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_4 | spl7_20)),
% 0.20/0.49    inference(resolution,[],[f236,f230])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    ( ! [X0] : (sP6(X0,sK0) | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))) ) | ~spl7_4),
% 0.20/0.49    inference(resolution,[],[f84,f65])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ~spl7_22 | spl7_23 | ~spl7_1 | ~spl7_3 | ~spl7_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f257,f97,f77,f68,f252,f248])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl7_1 <=> v2_funct_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl7_7 <=> v1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2) | sK3 = X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1))) ) | (~spl7_1 | ~spl7_3 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f256,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    v1_relat_1(sK1) | ~spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ( ! [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2) | sK3 = X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f255,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    v1_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f29,f28])).
% 0.20/0.49  % (14271)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.49    inference(rectify,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ( ! [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2) | sK3 = X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f241,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    v2_funct_1(sK1) | ~spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    ( ! [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,sK2) | sK3 = X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl7_3),
% 0.20/0.49    inference(superposition,[],[f47,f79])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(rectify,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    ~spl7_20 | spl7_21 | ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f226,f68,f232,f228])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f225,f38])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f107,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f40,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP6(X3,X0)) )),
% 0.20/0.49    inference(general_splitting,[],[f62,f65_D])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    $false | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f98])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f175,f38])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ~v2_funct_1(sK1) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f173])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(superposition,[],[f51,f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    sK4(sK1) = sK5(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f166,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),sK0) | (spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f155,f98])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),sK0) | ~v1_relat_1(sK1) | spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f154,f38])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f70])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f129,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(X1,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f126,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f40])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.49    inference(superposition,[],[f60,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f40,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(equality_resolution,[],[f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0) ) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f158,f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),sK0) | (spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f152,f98])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),sK0) | ~v1_relat_1(sK1) | spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f151,f38])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f149,f70])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f129,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(sK1),sK0) | sK5(sK1) = X0) ) | (~spl7_6 | ~spl7_8)),
% 0.20/0.49    inference(superposition,[],[f93,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl7_8 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ~spl7_11 | spl7_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f130,f136,f132])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK1) | ~r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.49    inference(resolution,[],[f128,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.20/0.49    inference(resolution,[],[f126,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl7_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    $false | spl7_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f106,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f40,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ~spl7_7 | spl7_1 | spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f95,f101,f68,f97])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f38,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl7_1 | spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f92,f68])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~spl7_1 | spl7_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f87,f68])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~spl7_1 | spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f82,f68])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~spl7_1 | spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f77,f68])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f72,f68])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (14267)------------------------------
% 0.20/0.49  % (14267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14267)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (14267)Memory used [KB]: 10746
% 0.20/0.49  % (14267)Time elapsed: 0.087 s
% 0.20/0.49  % (14267)------------------------------
% 0.20/0.49  % (14267)------------------------------
% 0.20/0.49  % (14277)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (14265)Success in time 0.146 s
%------------------------------------------------------------------------------
