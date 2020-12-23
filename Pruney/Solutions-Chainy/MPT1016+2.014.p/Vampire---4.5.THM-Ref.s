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
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 318 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   15
%              Number of atoms          :  522 (2147 expanded)
%              Number of equality atoms :  109 ( 589 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f85,f96,f104,f106,f120,f128,f130,f139,f143,f148,f156,f216,f240])).

fof(f240,plain,
    ( ~ spl7_5
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(resolution,[],[f230,f46])).

% (29774)Termination reason: Refutation not found, incomplete strategy

% (29774)Memory used [KB]: 10618
% (29774)Time elapsed: 0.165 s
% (29774)------------------------------
% (29774)------------------------------
% (29775)Refutation not found, incomplete strategy% (29775)------------------------------
% (29775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f158,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f158,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f79,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f79,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f216,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f67,f209])).

fof(f209,plain,
    ( sK2 = sK3
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f182,f179])).

fof(f179,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(resolution,[],[f152,f79])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f182,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f178,f71])).

fof(f71,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f178,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(resolution,[],[f152,f75])).

fof(f75,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f67,plain,
    ( sK2 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f156,plain,
    ( ~ spl7_1
    | spl7_15
    | spl7_16 ),
    inference(avatar_split_clause,[],[f149,f154,f151,f63])).

fof(f63,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f149,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(global_subsumption,[],[f39,f38,f97])).

% (29785)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (29778)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f97,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f148,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f147,f137,f63,f91,f88])).

fof(f88,plain,
    ( spl7_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f91,plain,
    ( spl7_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f137,plain,
    ( spl7_14
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f147,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_14 ),
    inference(superposition,[],[f51,f138])).

fof(f138,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f51,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f143,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_12
    | spl7_13 ),
    inference(avatar_split_clause,[],[f141,f134,f126,f63,f91,f88])).

fof(f126,plain,
    ( spl7_12
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f134,plain,
    ( spl7_13
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f141,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_13 ),
    inference(resolution,[],[f140,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_13 ),
    inference(resolution,[],[f135,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f135,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f139,plain,
    ( ~ spl7_13
    | spl7_14
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f132,f117,f137,f134])).

fof(f117,plain,
    ( spl7_11
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f132,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ spl7_11 ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f130,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f122,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f122,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f108,f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(global_subsumption,[],[f40,f107])).

fof(f107,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f60,f98])).

fof(f98,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f128,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_12
    | spl7_10 ),
    inference(avatar_split_clause,[],[f123,f114,f126,f63,f91,f88])).

fof(f114,plain,
    ( spl7_10
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f123,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_10 ),
    inference(resolution,[],[f121,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_10 ),
    inference(resolution,[],[f115,f52])).

fof(f115,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f120,plain,
    ( ~ spl7_10
    | spl7_11
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f110,f94,f83,f117,f114])).

% (29775)Termination reason: Refutation not found, incomplete strategy
fof(f83,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

% (29775)Memory used [KB]: 10618
fof(f94,plain,
    ( spl7_9
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

% (29775)Time elapsed: 0.156 s
% (29775)------------------------------
% (29775)------------------------------
fof(f110,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(sK5(sK1),sK0)
        | ~ r2_hidden(X1,sK0)
        | sK5(sK1) = X1 )
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(superposition,[],[f84,f95])).

fof(f95,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f84,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f38,f92])).

fof(f92,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f104,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f89,f99])).

fof(f99,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f86,f63,f94,f91,f88])).

fof(f86,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(resolution,[],[f64,f50])).

% (29792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f85,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f41,f83,f63])).

fof(f41,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f42,f78,f63])).

fof(f42,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f43,f74,f63])).

fof(f43,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f44,f70,f63])).

fof(f44,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f45,f66,f63])).

fof(f45,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (29765)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (29765)Refutation not found, incomplete strategy% (29765)------------------------------
% 0.20/0.52  % (29765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29765)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29765)Memory used [KB]: 1663
% 0.20/0.52  % (29765)Time elapsed: 0.116 s
% 0.20/0.52  % (29765)------------------------------
% 0.20/0.52  % (29765)------------------------------
% 0.20/0.53  % (29768)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (29779)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (29772)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (29780)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (29769)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (29766)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (29771)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (29784)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (29789)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (29782)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (29787)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (29782)Refutation not found, incomplete strategy% (29782)------------------------------
% 0.20/0.55  % (29782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29782)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29782)Memory used [KB]: 10618
% 0.20/0.55  % (29782)Time elapsed: 0.137 s
% 0.20/0.55  % (29782)------------------------------
% 0.20/0.55  % (29782)------------------------------
% 0.20/0.55  % (29770)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (29790)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (29781)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (29773)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (29791)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (29794)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (29776)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (29767)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (29788)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (29767)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (29793)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (29786)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (29774)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (29776)Refutation not found, incomplete strategy% (29776)------------------------------
% 0.20/0.57  % (29776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (29776)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (29776)Memory used [KB]: 10618
% 0.20/0.57  % (29776)Time elapsed: 0.151 s
% 0.20/0.57  % (29776)------------------------------
% 0.20/0.57  % (29776)------------------------------
% 0.20/0.57  % (29774)Refutation not found, incomplete strategy% (29774)------------------------------
% 0.20/0.57  % (29774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (29783)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (29775)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f241,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f85,f96,f104,f106,f120,f128,f130,f139,f143,f148,f156,f216,f240])).
% 1.48/0.57  fof(f240,plain,(
% 1.48/0.57    ~spl7_5 | ~spl7_16),
% 1.48/0.57    inference(avatar_contradiction_clause,[],[f239])).
% 1.48/0.57  fof(f239,plain,(
% 1.48/0.57    $false | (~spl7_5 | ~spl7_16)),
% 1.48/0.57    inference(resolution,[],[f230,f46])).
% 1.48/0.57  % (29774)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (29774)Memory used [KB]: 10618
% 1.48/0.57  % (29774)Time elapsed: 0.165 s
% 1.48/0.57  % (29774)------------------------------
% 1.48/0.57  % (29774)------------------------------
% 1.48/0.58  % (29775)Refutation not found, incomplete strategy% (29775)------------------------------
% 1.48/0.58  % (29775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  fof(f46,plain,(
% 1.48/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.58  fof(f230,plain,(
% 1.48/0.58    ~r1_tarski(k1_xboole_0,sK2) | (~spl7_5 | ~spl7_16)),
% 1.48/0.58    inference(backward_demodulation,[],[f158,f155])).
% 1.48/0.58  fof(f155,plain,(
% 1.48/0.58    k1_xboole_0 = sK0 | ~spl7_16),
% 1.48/0.58    inference(avatar_component_clause,[],[f154])).
% 1.48/0.58  fof(f154,plain,(
% 1.48/0.58    spl7_16 <=> k1_xboole_0 = sK0),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.48/0.58  fof(f158,plain,(
% 1.48/0.58    ~r1_tarski(sK0,sK2) | ~spl7_5),
% 1.48/0.58    inference(resolution,[],[f79,f57])).
% 1.48/0.58  fof(f57,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f17])).
% 1.48/0.58  fof(f17,plain,(
% 1.48/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.48/0.58  fof(f79,plain,(
% 1.48/0.58    r2_hidden(sK2,sK0) | ~spl7_5),
% 1.48/0.58    inference(avatar_component_clause,[],[f78])).
% 1.48/0.58  fof(f78,plain,(
% 1.48/0.58    spl7_5 <=> r2_hidden(sK2,sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.48/0.58  fof(f216,plain,(
% 1.48/0.58    spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f210])).
% 1.48/0.58  fof(f210,plain,(
% 1.48/0.58    $false | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15)),
% 1.48/0.58    inference(subsumption_resolution,[],[f67,f209])).
% 1.48/0.58  fof(f209,plain,(
% 1.48/0.58    sK2 = sK3 | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15)),
% 1.48/0.58    inference(forward_demodulation,[],[f182,f179])).
% 1.48/0.58  fof(f179,plain,(
% 1.48/0.58    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_5 | ~spl7_15)),
% 1.48/0.58    inference(resolution,[],[f152,f79])).
% 1.48/0.58  fof(f152,plain,(
% 1.48/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl7_15),
% 1.48/0.58    inference(avatar_component_clause,[],[f151])).
% 1.48/0.58  fof(f151,plain,(
% 1.48/0.58    spl7_15 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.48/0.58  fof(f182,plain,(
% 1.48/0.58    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_3 | ~spl7_4 | ~spl7_15)),
% 1.48/0.58    inference(forward_demodulation,[],[f178,f71])).
% 1.48/0.58  fof(f71,plain,(
% 1.48/0.58    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 1.48/0.58    inference(avatar_component_clause,[],[f70])).
% 1.48/0.58  fof(f70,plain,(
% 1.48/0.58    spl7_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.48/0.58  fof(f178,plain,(
% 1.48/0.58    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_4 | ~spl7_15)),
% 1.48/0.58    inference(resolution,[],[f152,f75])).
% 1.48/0.58  fof(f75,plain,(
% 1.48/0.58    r2_hidden(sK3,sK0) | ~spl7_4),
% 1.48/0.58    inference(avatar_component_clause,[],[f74])).
% 1.48/0.58  fof(f74,plain,(
% 1.48/0.58    spl7_4 <=> r2_hidden(sK3,sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.48/0.58  fof(f67,plain,(
% 1.48/0.58    sK2 != sK3 | spl7_2),
% 1.48/0.58    inference(avatar_component_clause,[],[f66])).
% 1.48/0.58  fof(f66,plain,(
% 1.48/0.58    spl7_2 <=> sK2 = sK3),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.48/0.58  fof(f156,plain,(
% 1.48/0.58    ~spl7_1 | spl7_15 | spl7_16),
% 1.48/0.58    inference(avatar_split_clause,[],[f149,f154,f151,f63])).
% 1.48/0.58  fof(f63,plain,(
% 1.48/0.58    spl7_1 <=> v2_funct_1(sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.48/0.58  fof(f149,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.48/0.58    inference(global_subsumption,[],[f39,f38,f97])).
% 1.48/0.58  % (29785)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.58  % (29778)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.58  fof(f97,plain,(
% 1.48/0.58    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.48/0.58    inference(resolution,[],[f40,f61])).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f22])).
% 1.48/0.58  fof(f22,plain,(
% 1.48/0.58    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.48/0.58    inference(flattening,[],[f21])).
% 1.48/0.58  fof(f21,plain,(
% 1.48/0.58    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.48/0.58    inference(ennf_transformation,[],[f9])).
% 1.48/0.58  fof(f9,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 1.48/0.58  fof(f40,plain,(
% 1.48/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f28,plain,(
% 1.48/0.58    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27,f26])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.48/0.58    inference(rectify,[],[f24])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.48/0.58    inference(flattening,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.48/0.58    inference(nnf_transformation,[],[f13])).
% 1.48/0.58  fof(f13,plain,(
% 1.48/0.58    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.48/0.58    inference(flattening,[],[f12])).
% 1.48/0.58  fof(f12,plain,(
% 1.48/0.58    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,negated_conjecture,(
% 1.48/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.48/0.58    inference(negated_conjecture,[],[f10])).
% 1.48/0.58  fof(f10,conjecture,(
% 1.48/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 1.48/0.58  fof(f38,plain,(
% 1.48/0.58    v1_funct_1(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f39,plain,(
% 1.48/0.58    v1_funct_2(sK1,sK0,sK0)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f148,plain,(
% 1.48/0.58    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_14),
% 1.48/0.58    inference(avatar_split_clause,[],[f147,f137,f63,f91,f88])).
% 1.48/0.58  fof(f88,plain,(
% 1.48/0.58    spl7_7 <=> v1_relat_1(sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.48/0.58  fof(f91,plain,(
% 1.48/0.58    spl7_8 <=> v1_funct_1(sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.48/0.58  fof(f137,plain,(
% 1.48/0.58    spl7_14 <=> sK4(sK1) = sK5(sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.48/0.58  fof(f147,plain,(
% 1.48/0.58    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_14),
% 1.48/0.58    inference(trivial_inequality_removal,[],[f146])).
% 1.48/0.58  fof(f146,plain,(
% 1.48/0.58    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_14),
% 1.48/0.58    inference(superposition,[],[f51,f138])).
% 1.48/0.58  fof(f138,plain,(
% 1.48/0.58    sK4(sK1) = sK5(sK1) | ~spl7_14),
% 1.48/0.58    inference(avatar_component_clause,[],[f137])).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f31])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f30,plain,(
% 1.48/0.58    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(rectify,[],[f29])).
% 1.48/0.58  fof(f29,plain,(
% 1.48/0.58    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(nnf_transformation,[],[f15])).
% 1.48/0.58  fof(f15,plain,(
% 1.48/0.58    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(flattening,[],[f14])).
% 1.48/0.58  fof(f14,plain,(
% 1.48/0.58    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.48/0.58  fof(f143,plain,(
% 1.48/0.58    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_12 | spl7_13),
% 1.48/0.58    inference(avatar_split_clause,[],[f141,f134,f126,f63,f91,f88])).
% 1.48/0.58  fof(f126,plain,(
% 1.48/0.58    spl7_12 <=> r1_tarski(k1_relat_1(sK1),sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.48/0.58  fof(f134,plain,(
% 1.48/0.58    spl7_13 <=> r2_hidden(sK4(sK1),sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.48/0.58  fof(f141,plain,(
% 1.48/0.58    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_13),
% 1.48/0.58    inference(resolution,[],[f140,f48])).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f140,plain,(
% 1.48/0.58    ( ! [X0] : (~r2_hidden(sK4(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_13),
% 1.48/0.58    inference(resolution,[],[f135,f52])).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f36])).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.48/0.58    introduced(choice_axiom,[])).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(rectify,[],[f33])).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.58    inference(nnf_transformation,[],[f16])).
% 1.48/0.58  fof(f16,plain,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.58    inference(ennf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.58  fof(f135,plain,(
% 1.48/0.58    ~r2_hidden(sK4(sK1),sK0) | spl7_13),
% 1.48/0.58    inference(avatar_component_clause,[],[f134])).
% 1.48/0.58  fof(f139,plain,(
% 1.48/0.58    ~spl7_13 | spl7_14 | ~spl7_11),
% 1.48/0.58    inference(avatar_split_clause,[],[f132,f117,f137,f134])).
% 1.48/0.58  fof(f117,plain,(
% 1.48/0.58    spl7_11 <=> ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.48/0.58  fof(f132,plain,(
% 1.48/0.58    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~spl7_11),
% 1.48/0.58    inference(equality_resolution,[],[f118])).
% 1.48/0.58  fof(f118,plain,(
% 1.48/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl7_11),
% 1.48/0.58    inference(avatar_component_clause,[],[f117])).
% 1.48/0.58  fof(f130,plain,(
% 1.48/0.58    spl7_12),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f129])).
% 1.48/0.58  fof(f129,plain,(
% 1.48/0.58    $false | spl7_12),
% 1.48/0.58    inference(subsumption_resolution,[],[f122,f127])).
% 1.48/0.58  fof(f127,plain,(
% 1.48/0.58    ~r1_tarski(k1_relat_1(sK1),sK0) | spl7_12),
% 1.48/0.58    inference(avatar_component_clause,[],[f126])).
% 1.48/0.58  fof(f122,plain,(
% 1.48/0.58    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.48/0.58    inference(resolution,[],[f108,f55])).
% 1.48/0.58  fof(f55,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f37])).
% 1.48/0.58  fof(f37,plain,(
% 1.48/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.48/0.58    inference(nnf_transformation,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.58  fof(f108,plain,(
% 1.48/0.58    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.48/0.58    inference(global_subsumption,[],[f40,f107])).
% 1.48/0.58  fof(f107,plain,(
% 1.48/0.58    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.58    inference(superposition,[],[f60,f98])).
% 1.48/0.58  fof(f98,plain,(
% 1.48/0.58    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.48/0.58    inference(resolution,[],[f40,f59])).
% 1.48/0.58  fof(f59,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f8])).
% 1.48/0.58  fof(f8,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.58  fof(f60,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f20])).
% 1.48/0.58  fof(f20,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f7])).
% 1.48/0.58  fof(f7,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.48/0.58  fof(f128,plain,(
% 1.48/0.58    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_12 | spl7_10),
% 1.48/0.58    inference(avatar_split_clause,[],[f123,f114,f126,f63,f91,f88])).
% 1.48/0.58  fof(f114,plain,(
% 1.48/0.58    spl7_10 <=> r2_hidden(sK5(sK1),sK0)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.48/0.58  fof(f123,plain,(
% 1.48/0.58    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_10),
% 1.48/0.58    inference(resolution,[],[f121,f49])).
% 1.48/0.58  fof(f49,plain,(
% 1.48/0.58    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f121,plain,(
% 1.48/0.58    ( ! [X0] : (~r2_hidden(sK5(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_10),
% 1.48/0.58    inference(resolution,[],[f115,f52])).
% 1.48/0.58  fof(f115,plain,(
% 1.48/0.58    ~r2_hidden(sK5(sK1),sK0) | spl7_10),
% 1.48/0.58    inference(avatar_component_clause,[],[f114])).
% 1.48/0.58  fof(f120,plain,(
% 1.48/0.58    ~spl7_10 | spl7_11 | ~spl7_6 | ~spl7_9),
% 1.48/0.58    inference(avatar_split_clause,[],[f110,f94,f83,f117,f114])).
% 1.48/0.58  % (29775)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  fof(f83,plain,(
% 1.48/0.58    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.48/0.58  
% 1.48/0.58  % (29775)Memory used [KB]: 10618
% 1.48/0.58  fof(f94,plain,(
% 1.48/0.58    spl7_9 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.48/0.58  % (29775)Time elapsed: 0.156 s
% 1.48/0.58  % (29775)------------------------------
% 1.48/0.58  % (29775)------------------------------
% 1.48/0.58  fof(f110,plain,(
% 1.48/0.58    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X1,sK0) | sK5(sK1) = X1) ) | (~spl7_6 | ~spl7_9)),
% 1.48/0.58    inference(superposition,[],[f84,f95])).
% 1.48/0.58  fof(f95,plain,(
% 1.48/0.58    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_9),
% 1.48/0.58    inference(avatar_component_clause,[],[f94])).
% 1.48/0.58  fof(f84,plain,(
% 1.48/0.58    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl7_6),
% 1.48/0.58    inference(avatar_component_clause,[],[f83])).
% 1.48/0.58  fof(f106,plain,(
% 1.48/0.58    spl7_8),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f105])).
% 1.48/0.58  fof(f105,plain,(
% 1.48/0.58    $false | spl7_8),
% 1.48/0.58    inference(subsumption_resolution,[],[f38,f92])).
% 1.48/0.58  fof(f92,plain,(
% 1.48/0.58    ~v1_funct_1(sK1) | spl7_8),
% 1.48/0.58    inference(avatar_component_clause,[],[f91])).
% 1.48/0.58  fof(f104,plain,(
% 1.48/0.58    spl7_7),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f103])).
% 1.48/0.58  fof(f103,plain,(
% 1.48/0.58    $false | spl7_7),
% 1.48/0.58    inference(subsumption_resolution,[],[f89,f99])).
% 1.48/0.58  fof(f99,plain,(
% 1.48/0.58    v1_relat_1(sK1)),
% 1.48/0.58    inference(resolution,[],[f40,f58])).
% 1.48/0.58  fof(f58,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f18])).
% 1.48/0.58  fof(f18,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.58    inference(ennf_transformation,[],[f6])).
% 1.48/0.58  fof(f6,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.58  fof(f89,plain,(
% 1.48/0.58    ~v1_relat_1(sK1) | spl7_7),
% 1.48/0.58    inference(avatar_component_clause,[],[f88])).
% 1.48/0.58  fof(f96,plain,(
% 1.48/0.58    ~spl7_7 | ~spl7_8 | spl7_9 | spl7_1),
% 1.48/0.58    inference(avatar_split_clause,[],[f86,f63,f94,f91,f88])).
% 1.48/0.58  fof(f86,plain,(
% 1.48/0.58    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 1.48/0.58    inference(resolution,[],[f64,f50])).
% 1.48/0.58  % (29792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.58  fof(f50,plain,(
% 1.48/0.58    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f32])).
% 1.48/0.58  fof(f64,plain,(
% 1.48/0.58    ~v2_funct_1(sK1) | spl7_1),
% 1.48/0.58    inference(avatar_component_clause,[],[f63])).
% 1.48/0.58  fof(f85,plain,(
% 1.48/0.58    spl7_1 | spl7_6),
% 1.48/0.58    inference(avatar_split_clause,[],[f41,f83,f63])).
% 1.48/0.58  fof(f41,plain,(
% 1.48/0.58    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f80,plain,(
% 1.48/0.58    ~spl7_1 | spl7_5),
% 1.48/0.58    inference(avatar_split_clause,[],[f42,f78,f63])).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    ~spl7_1 | spl7_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f43,f74,f63])).
% 1.48/0.58  fof(f43,plain,(
% 1.48/0.58    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f72,plain,(
% 1.48/0.58    ~spl7_1 | spl7_3),
% 1.48/0.58    inference(avatar_split_clause,[],[f44,f70,f63])).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  fof(f68,plain,(
% 1.48/0.58    ~spl7_1 | ~spl7_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f45,f66,f63])).
% 1.48/0.58  fof(f45,plain,(
% 1.48/0.58    sK2 != sK3 | ~v2_funct_1(sK1)),
% 1.48/0.58    inference(cnf_transformation,[],[f28])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (29767)------------------------------
% 1.48/0.58  % (29767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (29767)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (29767)Memory used [KB]: 10874
% 1.48/0.58  % (29767)Time elapsed: 0.150 s
% 1.48/0.58  % (29767)------------------------------
% 1.48/0.58  % (29767)------------------------------
% 1.48/0.59  % (29777)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.59  % (29764)Success in time 0.222 s
%------------------------------------------------------------------------------
