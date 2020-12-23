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
% DateTime   : Thu Dec  3 13:06:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 (1652 expanded)
%              Number of leaves         :   17 ( 499 expanded)
%              Depth                    :   30
%              Number of atoms          :  410 (11374 expanded)
%              Number of equality atoms :   71 (2593 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f299])).

fof(f299,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f298,f234])).

fof(f234,plain,(
    ! [X1] : sP2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f186,f228])).

fof(f228,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f225,f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f225,plain,(
    v1_xboole_0(sK5) ),
    inference(resolution,[],[f185,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f89])).

fof(f89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f60,f87])).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f61,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

% (25185)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f185,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f167,f83])).

fof(f167,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f48,f165])).

fof(f165,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f162,f57])).

fof(f162,plain,(
    v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f161,f112])).

fof(f112,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f109,f48])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(sK5,X0,X1) ) ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_partfun1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f19,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

% (25186)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f161,plain,
    ( v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f160,f54])).

fof(f54,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,
    ( r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    | v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f155,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f155,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK3,sK5,X0)
      | r2_hidden(sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f152,f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f152,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f151,f51])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f28])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | sP0(sK5,sK3,sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f149,f136])).

fof(f136,plain,
    ( v1_partfun1(sK6,sK3)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f134,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK6,X0)
      | sP0(sK5,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f147,f49])).

fof(f147,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f86,f52])).

fof(f52,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_partfun1(X0,X4)
      | sP0(X0,X1,X4,X3)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).

fof(f43,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f28])).

fof(f186,plain,(
    ! [X1] : sP2(sK5,k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f114,f185])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
      | sP2(sK5,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f109,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f298,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))
      | ~ sP2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f291,f85])).

fof(f291,plain,(
    ! [X2,X1] :
      ( ~ sP1(X2,k1_xboole_0,k1_xboole_0,X1)
      | r2_hidden(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f289,f70])).

fof(f289,plain,(
    ! [X0] : sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f288,f102])).

fof(f102,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f92,f98])).

fof(f98,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f95,f57])).

fof(f95,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f94,f92])).

fof(f92,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f56,f83])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f287,f84])).

fof(f287,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f280,f107])).

fof(f107,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f55,f98])).

fof(f55,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(k1_xboole_0,X0,k1_xboole_0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f279,f256])).

fof(f256,plain,(
    k1_xboole_0 = sK6 ),
    inference(resolution,[],[f253,f57])).

fof(f253,plain,(
    v1_xboole_0(sK6) ),
    inference(resolution,[],[f189,f94])).

fof(f189,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f169,f83])).

fof(f169,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f51,f165])).

fof(f279,plain,(
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
    inference(backward_demodulation,[],[f232,f256])).

fof(f232,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f149,f228])).

fof(f269,plain,(
    ~ r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f236,f256])).

fof(f236,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f192,f228])).

fof(f192,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5)) ),
    inference(forward_demodulation,[],[f170,f166])).

fof(f166,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f53,f165])).

fof(f53,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f170,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f54,f165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:00:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (25167)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (25176)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (25177)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (25171)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (25175)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (25167)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (25174)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (25168)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (25187)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (25182)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (25178)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (25179)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (25164)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (25184)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25180)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (25169)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (25170)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (25165)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (25165)Refutation not found, incomplete strategy% (25165)------------------------------
% 0.22/0.53  % (25165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25173)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f269,f299])).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f298,f234])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ( ! [X1] : (sP2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f186,f228])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    k1_xboole_0 = sK5),
% 0.22/0.54    inference(resolution,[],[f225,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    v1_xboole_0(sK5)),
% 0.22/0.54    inference(resolution,[],[f185,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f58,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(resolution,[],[f60,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f61,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (25185)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    inference(forward_demodulation,[],[f167,f83])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f48,f165])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    k1_xboole_0 = sK4),
% 0.22/0.54    inference(resolution,[],[f162,f57])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    v1_xboole_0(sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    sP2(sK5,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f109,f48])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(sK5,X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f79,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v1_funct_1(sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f27,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(definition_folding,[],[f19,f24,f23,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  % (25186)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f160,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) | v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f155,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(equality_resolution,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 0.22/0.54    inference(rectify,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ( ! [X0] : (~sP1(sK4,sK3,sK5,X0) | r2_hidden(sK6,X0) | v1_xboole_0(sK4)) )),
% 0.22/0.54    inference(resolution,[],[f152,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3) | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    sP0(sK5,sK3,sK6,sK4) | v1_xboole_0(sK4)),
% 0.22/0.54    inference(resolution,[],[f151,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | sP0(sK5,sK3,sK6,X0) | v1_xboole_0(sK4)) )),
% 0.22/0.54    inference(resolution,[],[f149,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    v1_partfun1(sK6,sK3) | v1_xboole_0(sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f135,f51])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    v1_partfun1(sK6,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f134,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v1_funct_1(sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    v1_partfun1(sK6,sK3) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.22/0.54    inference(resolution,[],[f63,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    v1_funct_2(sK6,sK3,sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_partfun1(sK6,X0) | sP0(sK5,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f49])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(sK5,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK6)) )),
% 0.22/0.54    inference(resolution,[],[f86,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    r1_partfun1(sK5,sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X4,X0,X3,X1] : (~r1_partfun1(X0,X4) | sP0(X0,X1,X4,X3) | ~v1_partfun1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.54    inference(equality_resolution,[],[f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ( ! [X1] : (sP2(sK5,k1_xboole_0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f114,f185])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | sP2(sK5,k1_xboole_0,X1)) )),
% 0.22/0.54    inference(superposition,[],[f109,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) | ~sP2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f291,f85])).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~sP1(X2,k1_xboole_0,k1_xboole_0,X1) | r2_hidden(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f289,f70])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f288,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    inference(backward_demodulation,[],[f92,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.22/0.54    inference(resolution,[],[f95,f57])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 0.22/0.54    inference(resolution,[],[f94,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    inference(superposition,[],[f56,f83])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f287,f84])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.54    inference(resolution,[],[f280,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(superposition,[],[f55,f98])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f279,f256])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    k1_xboole_0 = sK6),
% 0.22/0.54    inference(resolution,[],[f253,f57])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    v1_xboole_0(sK6)),
% 0.22/0.54    inference(resolution,[],[f189,f94])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    inference(forward_demodulation,[],[f169,f83])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f51,f165])).
% 0.22/0.54  fof(f279,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~v1_partfun1(k1_xboole_0,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f268,f256])).
% 0.22/0.54  fof(f268,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f232,f256])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f149,f228])).
% 0.22/0.54  fof(f269,plain,(
% 0.22/0.54    ~r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(backward_demodulation,[],[f236,f256])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(backward_demodulation,[],[f192,f228])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5))),
% 0.22/0.54    inference(forward_demodulation,[],[f170,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f53,f165])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    k1_xboole_0 != sK4 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ~r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5))),
% 0.22/0.54    inference(backward_demodulation,[],[f54,f165])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (25167)------------------------------
% 0.22/0.54  % (25167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25167)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (25167)Memory used [KB]: 6396
% 0.22/0.54  % (25167)Time elapsed: 0.095 s
% 0.22/0.54  % (25167)------------------------------
% 0.22/0.54  % (25167)------------------------------
% 0.22/0.54  % (25163)Success in time 0.171 s
%------------------------------------------------------------------------------
