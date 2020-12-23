%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:55 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  123 (1690 expanded)
%              Number of leaves         :   19 ( 519 expanded)
%              Depth                    :   30
%              Number of atoms          :  427 (11354 expanded)
%              Number of equality atoms :   72 (2593 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f301])).

% (26541)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f301,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f300,f231])).

fof(f231,plain,(
    ! [X1] : sP2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f178,f225])).

fof(f225,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f221,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f221,plain,(
    v1_xboole_0(sK5) ),
    inference(resolution,[],[f177,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f93,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f85])).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f79,f84])).

fof(f84,plain,(
    k1_xboole_0 = sK10 ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,(
    v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f45])).

% (26522)Refutation not found, incomplete strategy% (26522)------------------------------
% (26522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26522)Termination reason: Refutation not found, incomplete strategy

% (26522)Memory used [KB]: 10746
% (26522)Time elapsed: 0.100 s
% (26522)------------------------------
% (26522)------------------------------
fof(f45,plain,(
    v1_xboole_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3,f44])).

fof(f44,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK10) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f177,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f158,f80])).

fof(f158,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f47,f156])).

fof(f156,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f153,f56])).

fof(f153,plain,(
    v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f152,f115])).

fof(f115,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f112,f47])).

% (26534)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(sK5,X0,X1) ) ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_partfun1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))
          & ( k1_xboole_0 = sK3
            | k1_xboole_0 != sK4 )
          & r1_partfun1(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))
        & ( k1_xboole_0 = sK3
          | k1_xboole_0 != sK4 )
        & r1_partfun1(sK5,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_partfun1(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f19,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f152,plain,
    ( v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f151,f53])).

fof(f53,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,
    ( r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    | v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f146,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f146,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK3,sK5,X0)
      | r2_hidden(sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f143,f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP1(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X2,X0,X4,X1) )
            & ( sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f143,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f142,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | sP0(sK5,sK3,sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f140,f127])).

fof(f127,plain,
    ( v1_partfun1(sK6,sK3)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f126,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f48,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK6,X0)
      | sP0(sK5,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_partfun1(X0,X4)
      | sP0(X0,X1,X4,X3)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
          & v1_partfun1(sK9(X0,X1,X2,X3),X1)
          & sK9(X0,X1,X2,X3) = X2
          & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK9(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
        & v1_partfun1(sK9(X0,X1,X2,X3),X1)
        & sK9(X0,X1,X2,X3) = X2
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK9(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ? [X5] :
            ( r1_partfun1(X0,X5)
            & v1_partfun1(X5,X1)
            & X2 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            & v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP0(X2,X0,X4,X1)
        | ! [X5] :
            ( ~ r1_partfun1(X2,X5)
            | ~ v1_partfun1(X5,X0)
            | X4 != X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_1(X5) ) )
      & ( ? [X5] :
            ( r1_partfun1(X2,X5)
            & v1_partfun1(X5,X0)
            & X4 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X5) )
        | ~ sP0(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f178,plain,(
    ! [X1] : sP2(sK5,k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f117,f177])).

fof(f117,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
      | sP2(sK5,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f112,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f300,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))
      | ~ sP2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f293,f82])).

fof(f293,plain,(
    ! [X2,X1] :
      ( ~ sP1(X2,k1_xboole_0,k1_xboole_0,X1)
      | r2_hidden(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f291,f68])).

fof(f291,plain,(
    ! [X0] : sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f290,f102])).

fof(f102,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f88,f97])).

fof(f97,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f92,f56])).

fof(f92,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f90,f88])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f78,f85])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f88,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f55,f80])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f289,f81])).

fof(f289,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f281,f107])).

fof(f107,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f54,f97])).

fof(f54,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(k1_xboole_0,X0,k1_xboole_0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f280,f256])).

fof(f256,plain,(
    k1_xboole_0 = sK6 ),
    inference(resolution,[],[f252,f56])).

fof(f252,plain,(
    v1_xboole_0(sK6) ),
    inference(resolution,[],[f181,f94])).

fof(f181,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f160,f80])).

fof(f160,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f50,f156])).

fof(f280,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X0,k1_xboole_0,X1)
      | ~ v1_partfun1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f268,f256])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(k1_xboole_0,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f229,f256])).

fof(f229,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f140,f225])).

fof(f269,plain,(
    ~ r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f233,f256])).

fof(f233,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f184,f225])).

fof(f184,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5)) ),
    inference(forward_demodulation,[],[f161,f157])).

fof(f157,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f52,f156])).

fof(f52,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f161,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f53,f156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26527)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (26525)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (26524)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (26532)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (26533)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (26543)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (26544)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (26526)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (26536)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (26535)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (26522)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.51  % (26542)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.27/0.51  % (26529)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.27/0.51  % (26524)Refutation found. Thanks to Tanya!
% 1.27/0.51  % SZS status Theorem for theBenchmark
% 1.27/0.51  % SZS output start Proof for theBenchmark
% 1.27/0.51  fof(f302,plain,(
% 1.27/0.51    $false),
% 1.27/0.51    inference(subsumption_resolution,[],[f269,f301])).
% 1.27/0.51  % (26541)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.27/0.51  fof(f301,plain,(
% 1.27/0.51    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))) )),
% 1.27/0.51    inference(subsumption_resolution,[],[f300,f231])).
% 1.27/0.51  fof(f231,plain,(
% 1.27/0.51    ( ! [X1] : (sP2(k1_xboole_0,k1_xboole_0,X1)) )),
% 1.27/0.51    inference(backward_demodulation,[],[f178,f225])).
% 1.27/0.51  fof(f225,plain,(
% 1.27/0.51    k1_xboole_0 = sK5),
% 1.27/0.51    inference(resolution,[],[f221,f56])).
% 1.27/0.51  fof(f56,plain,(
% 1.27/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.51    inference(cnf_transformation,[],[f14])).
% 1.27/0.51  fof(f14,plain,(
% 1.27/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f2])).
% 1.27/0.51  fof(f2,axiom,(
% 1.27/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.51  fof(f221,plain,(
% 1.27/0.51    v1_xboole_0(sK5)),
% 1.27/0.51    inference(resolution,[],[f177,f94])).
% 1.27/0.51  fof(f94,plain,(
% 1.27/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.27/0.51    inference(forward_demodulation,[],[f93,f80])).
% 1.27/0.51  fof(f80,plain,(
% 1.27/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.27/0.51    inference(equality_resolution,[],[f64])).
% 1.27/0.51  fof(f64,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.27/0.51    inference(cnf_transformation,[],[f33])).
% 1.27/0.51  fof(f33,plain,(
% 1.27/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.27/0.51    inference(flattening,[],[f32])).
% 1.27/0.51  fof(f32,plain,(
% 1.27/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.27/0.51    inference(nnf_transformation,[],[f4])).
% 1.27/0.51  fof(f4,axiom,(
% 1.27/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.27/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.27/0.51  fof(f93,plain,(
% 1.27/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 1.27/0.51    inference(resolution,[],[f61,f85])).
% 1.27/0.51  fof(f85,plain,(
% 1.27/0.51    v1_xboole_0(k1_xboole_0)),
% 1.27/0.51    inference(backward_demodulation,[],[f79,f84])).
% 1.27/0.51  fof(f84,plain,(
% 1.27/0.51    k1_xboole_0 = sK10),
% 1.27/0.51    inference(resolution,[],[f56,f79])).
% 1.27/0.51  fof(f79,plain,(
% 1.27/0.51    v1_xboole_0(sK10)),
% 1.27/0.51    inference(cnf_transformation,[],[f45])).
% 1.27/0.51  % (26522)Refutation not found, incomplete strategy% (26522)------------------------------
% 1.27/0.51  % (26522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.51  % (26522)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.51  
% 1.27/0.51  % (26522)Memory used [KB]: 10746
% 1.27/0.51  % (26522)Time elapsed: 0.100 s
% 1.27/0.51  % (26522)------------------------------
% 1.27/0.51  % (26522)------------------------------
% 1.27/0.51  fof(f45,plain,(
% 1.27/0.51    v1_xboole_0(sK10)),
% 1.27/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3,f44])).
% 1.27/0.51  fof(f44,plain,(
% 1.27/0.51    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK10)),
% 1.27/0.51    introduced(choice_axiom,[])).
% 1.27/0.51  fof(f3,axiom,(
% 1.27/0.51    ? [X0] : v1_xboole_0(X0)),
% 1.27/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 1.27/0.51  fof(f61,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f17])).
% 1.27/0.51  fof(f17,plain,(
% 1.27/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f6])).
% 1.27/0.51  fof(f6,axiom,(
% 1.27/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.27/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.27/0.51  fof(f177,plain,(
% 1.27/0.51    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.51    inference(forward_demodulation,[],[f158,f80])).
% 1.27/0.51  fof(f158,plain,(
% 1.27/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 1.27/0.51    inference(backward_demodulation,[],[f47,f156])).
% 1.27/0.51  fof(f156,plain,(
% 1.27/0.51    k1_xboole_0 = sK4),
% 1.27/0.51    inference(resolution,[],[f153,f56])).
% 1.27/0.51  fof(f153,plain,(
% 1.27/0.51    v1_xboole_0(sK4)),
% 1.27/0.51    inference(subsumption_resolution,[],[f152,f115])).
% 1.27/0.51  fof(f115,plain,(
% 1.27/0.51    sP2(sK5,sK3,sK4)),
% 1.27/0.51    inference(resolution,[],[f112,f47])).
% 1.27/0.52  % (26534)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.27/0.52  fof(f112,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(sK5,X0,X1)) )),
% 1.27/0.52    inference(resolution,[],[f77,f46])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    v1_funct_1(sK5)),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f27,plain,(
% 1.27/0.52    (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f26,f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f13,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.27/0.52    inference(flattening,[],[f12])).
% 1.27/0.52  fof(f12,plain,(
% 1.27/0.52    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.27/0.52    inference(ennf_transformation,[],[f11])).
% 1.27/0.52  fof(f11,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.27/0.52    inference(negated_conjecture,[],[f10])).
% 1.27/0.52  fof(f10,conjecture,(
% 1.27/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 1.27/0.52  fof(f77,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.52    inference(definition_folding,[],[f19,f23,f22,f21])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 1.27/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 1.27/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 1.27/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.52    inference(flattening,[],[f18])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.52    inference(ennf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 1.27/0.52  fof(f152,plain,(
% 1.27/0.52    v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 1.27/0.52    inference(subsumption_resolution,[],[f151,f53])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f151,plain,(
% 1.27/0.52    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) | v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 1.27/0.52    inference(resolution,[],[f146,f82])).
% 1.27/0.52  fof(f82,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 1.27/0.52    inference(equality_resolution,[],[f65])).
% 1.27/0.52  fof(f65,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f35])).
% 1.27/0.52  fof(f35,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 1.27/0.52    inference(rectify,[],[f34])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 1.27/0.52    inference(nnf_transformation,[],[f23])).
% 1.27/0.52  fof(f146,plain,(
% 1.27/0.52    ( ! [X0] : (~sP1(sK4,sK3,sK5,X0) | r2_hidden(sK6,X0) | v1_xboole_0(sK4)) )),
% 1.27/0.52    inference(resolution,[],[f143,f68])).
% 1.27/0.52  fof(f68,plain,(
% 1.27/0.52    ( ! [X2,X0,X5,X3,X1] : (~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f39])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).
% 1.27/0.52  fof(f38,plain,(
% 1.27/0.52    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.27/0.52    inference(rectify,[],[f36])).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 1.27/0.52    inference(nnf_transformation,[],[f22])).
% 1.27/0.52  fof(f143,plain,(
% 1.27/0.52    sP0(sK5,sK3,sK6,sK4) | v1_xboole_0(sK4)),
% 1.27/0.52    inference(resolution,[],[f142,f50])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f142,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | sP0(sK5,sK3,sK6,X0) | v1_xboole_0(sK4)) )),
% 1.27/0.52    inference(resolution,[],[f140,f127])).
% 1.27/0.52  fof(f127,plain,(
% 1.27/0.52    v1_partfun1(sK6,sK3) | v1_xboole_0(sK4)),
% 1.27/0.52    inference(subsumption_resolution,[],[f126,f50])).
% 1.27/0.52  fof(f126,plain,(
% 1.27/0.52    v1_partfun1(sK6,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 1.27/0.52    inference(subsumption_resolution,[],[f125,f48])).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    v1_funct_1(sK6)),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f125,plain,(
% 1.27/0.52    v1_partfun1(sK6,sK3) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 1.27/0.52    inference(resolution,[],[f60,f49])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    v1_funct_2(sK6,sK3,sK4)),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f60,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f16])).
% 1.27/0.52  fof(f16,plain,(
% 1.27/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.27/0.52    inference(flattening,[],[f15])).
% 1.27/0.52  fof(f15,plain,(
% 1.27/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.27/0.52  fof(f140,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v1_partfun1(sK6,X0) | sP0(sK5,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f138,f48])).
% 1.27/0.52  fof(f138,plain,(
% 1.27/0.52    ( ! [X0,X1] : (sP0(sK5,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK6)) )),
% 1.27/0.52    inference(resolution,[],[f83,f51])).
% 1.27/0.52  fof(f51,plain,(
% 1.27/0.52    r1_partfun1(sK5,sK6)),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f83,plain,(
% 1.27/0.52    ( ! [X4,X0,X3,X1] : (~r1_partfun1(X0,X4) | sP0(X0,X1,X4,X3) | ~v1_partfun1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 1.27/0.52    inference(equality_resolution,[],[f76])).
% 1.27/0.52  fof(f76,plain,(
% 1.27/0.52    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f43])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 1.27/0.52  fof(f42,plain,(
% 1.27/0.52    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 1.27/0.52    inference(rectify,[],[f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 1.27/0.52    inference(nnf_transformation,[],[f21])).
% 1.27/0.52  fof(f47,plain,(
% 1.27/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f178,plain,(
% 1.27/0.52    ( ! [X1] : (sP2(sK5,k1_xboole_0,X1)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f117,f177])).
% 1.27/0.52  fof(f117,plain,(
% 1.27/0.52    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | sP2(sK5,k1_xboole_0,X1)) )),
% 1.27/0.52    inference(superposition,[],[f112,f81])).
% 1.27/0.52  fof(f81,plain,(
% 1.27/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.27/0.52    inference(equality_resolution,[],[f63])).
% 1.27/0.52  fof(f63,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f33])).
% 1.27/0.52  fof(f300,plain,(
% 1.27/0.52    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) | ~sP2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.27/0.52    inference(resolution,[],[f293,f82])).
% 1.27/0.52  fof(f293,plain,(
% 1.27/0.52    ( ! [X2,X1] : (~sP1(X2,k1_xboole_0,k1_xboole_0,X1) | r2_hidden(k1_xboole_0,X1)) )),
% 1.27/0.52    inference(resolution,[],[f291,f68])).
% 1.27/0.52  fof(f291,plain,(
% 1.27/0.52    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f290,f102])).
% 1.27/0.52  fof(f102,plain,(
% 1.27/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.52    inference(backward_demodulation,[],[f88,f97])).
% 1.27/0.52  fof(f97,plain,(
% 1.27/0.52    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.27/0.52    inference(resolution,[],[f92,f56])).
% 1.27/0.52  fof(f92,plain,(
% 1.27/0.52    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.27/0.52    inference(resolution,[],[f91,f58])).
% 1.27/0.52  fof(f58,plain,(
% 1.27/0.52    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.52    inference(rectify,[],[f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.27/0.52    inference(nnf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.27/0.52  fof(f91,plain,(
% 1.27/0.52    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) )),
% 1.27/0.52    inference(resolution,[],[f90,f88])).
% 1.27/0.52  fof(f90,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.27/0.52    inference(resolution,[],[f78,f85])).
% 1.27/0.52  fof(f78,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f20])).
% 1.27/0.52  fof(f20,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.27/0.52  fof(f88,plain,(
% 1.27/0.52    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.52    inference(superposition,[],[f55,f80])).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.27/0.52  fof(f290,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 1.27/0.52    inference(forward_demodulation,[],[f289,f81])).
% 1.27/0.52  fof(f289,plain,(
% 1.27/0.52    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 1.27/0.52    inference(resolution,[],[f281,f107])).
% 1.27/0.52  fof(f107,plain,(
% 1.27/0.52    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.27/0.52    inference(superposition,[],[f54,f97])).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f9])).
% 1.27/0.52  fof(f281,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f280,f256])).
% 1.27/0.52  fof(f256,plain,(
% 1.27/0.52    k1_xboole_0 = sK6),
% 1.27/0.52    inference(resolution,[],[f252,f56])).
% 1.27/0.52  fof(f252,plain,(
% 1.27/0.52    v1_xboole_0(sK6)),
% 1.27/0.52    inference(resolution,[],[f181,f94])).
% 1.27/0.52  fof(f181,plain,(
% 1.27/0.52    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))),
% 1.27/0.52    inference(forward_demodulation,[],[f160,f80])).
% 1.27/0.52  fof(f160,plain,(
% 1.27/0.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 1.27/0.52    inference(backward_demodulation,[],[f50,f156])).
% 1.27/0.52  fof(f280,plain,(
% 1.27/0.52    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~v1_partfun1(k1_xboole_0,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f268,f256])).
% 1.27/0.52  fof(f268,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(backward_demodulation,[],[f229,f256])).
% 1.27/0.52  fof(f229,plain,(
% 1.27/0.52    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.52    inference(backward_demodulation,[],[f140,f225])).
% 1.27/0.52  fof(f269,plain,(
% 1.27/0.52    ~r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.27/0.52    inference(backward_demodulation,[],[f233,f256])).
% 1.27/0.52  fof(f233,plain,(
% 1.27/0.52    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.27/0.52    inference(backward_demodulation,[],[f184,f225])).
% 1.27/0.52  fof(f184,plain,(
% 1.27/0.52    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5))),
% 1.27/0.52    inference(forward_demodulation,[],[f161,f157])).
% 1.27/0.52  fof(f157,plain,(
% 1.27/0.52    k1_xboole_0 = sK3),
% 1.27/0.52    inference(subsumption_resolution,[],[f52,f156])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    k1_xboole_0 != sK4 | k1_xboole_0 = sK3),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f161,plain,(
% 1.27/0.52    ~r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5))),
% 1.27/0.52    inference(backward_demodulation,[],[f53,f156])).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (26524)------------------------------
% 1.27/0.52  % (26524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (26524)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (26524)Memory used [KB]: 6268
% 1.27/0.52  % (26524)Time elapsed: 0.102 s
% 1.27/0.52  % (26524)------------------------------
% 1.27/0.52  % (26524)------------------------------
% 1.27/0.52  % (26520)Success in time 0.171 s
%------------------------------------------------------------------------------
