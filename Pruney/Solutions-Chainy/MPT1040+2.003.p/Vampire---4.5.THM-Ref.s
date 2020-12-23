%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 906 expanded)
%              Number of leaves         :   13 ( 293 expanded)
%              Depth                    :   26
%              Number of atoms          :  411 (7528 expanded)
%              Number of equality atoms :   70 (1604 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(resolution,[],[f202,f30])).

fof(f30,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4))
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_partfun1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f9,f20,f19])).

fof(f19,plain,
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
          ( ~ r2_hidden(X3,k5_partfun1(sK2,sK3,sK4))
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & r1_partfun1(sK4,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,k5_partfun1(sK2,sK3,sK4))
        & ( k1_xboole_0 = sK2
          | k1_xboole_0 != sK3 )
        & r1_partfun1(sK4,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4))
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_partfun1(sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f202,plain,(
    ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f201,f32])).

fof(f32,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f201,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f200,f176])).

fof(f176,plain,(
    v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f146,f159])).

fof(f159,plain,(
    o_0_0_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2 ),
    inference(superposition,[],[f58,f140])).

fof(f140,plain,(
    o_0_0_xboole_0 = sK3 ),
    inference(resolution,[],[f139,f30])).

fof(f139,plain,
    ( ~ v1_funct_1(sK4)
    | o_0_0_xboole_0 = sK3 ),
    inference(resolution,[],[f133,f32])).

fof(f133,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | o_0_0_xboole_0 = sK3 ),
    inference(resolution,[],[f125,f33])).

fof(f33,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f125,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | o_0_0_xboole_0 = sK3 ),
    inference(resolution,[],[f116,f34])).

fof(f34,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f21])).

% (11800)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_2(sK5,sK2,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_1(sK5)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f95,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK5,sK2,X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK5) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK5,sK2,X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f80,plain,
    ( ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f79,f35])).

fof(f35,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,
    ( ~ r1_partfun1(sK4,sK5)
    | ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f74,plain,
    ( ~ sP1(sK3,sK2,sK4)
    | ~ v1_funct_1(sK5)
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_partfun1(sK5,sK2) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ r1_partfun1(sK4,sK5)
    | ~ sP1(sK3,sK2,sK4) ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2,k5_partfun1(sK2,sK3,sK4))
      | ~ v1_partfun1(sK5,X1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(sK5)
      | ~ r1_partfun1(X0,sK5) ) ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ~ r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK6(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
              & v1_partfun1(sK7(X0,X1,X2,X3),X1)
              & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
              & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK7(X0,X1,X2,X3)) )
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK8(X0,X1,X2,X7))
                & v1_partfun1(sK8(X0,X1,X2,X7),X1)
                & sK8(X0,X1,X2,X7) = X7
                & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK8(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK6(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK6(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & sK6(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X1)
        & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK8(X0,X1,X2,X7))
        & v1_partfun1(sK8(X0,X1,X2,X7),X1)
        & sK8(X0,X1,X2,X7) = X7
        & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK8(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
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
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f58,plain,
    ( o_0_0_xboole_0 != sK3
    | o_0_0_xboole_0 = sK2 ),
    inference(definition_unfolding,[],[f36,f54,f54])).

fof(f36,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,(
    v1_funct_2(sK5,sK2,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f33,f140])).

fof(f200,plain,
    ( ~ v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f180,f182])).

fof(f182,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(forward_demodulation,[],[f147,f159])).

fof(f147,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,o_0_0_xboole_0))) ),
    inference(backward_demodulation,[],[f34,f140])).

fof(f180,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(forward_demodulation,[],[f175,f159])).

fof(f175,plain,
    ( ~ v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(backward_demodulation,[],[f117,f159])).

fof(f117,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK5,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f95,f111])).

fof(f111,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f102,f30])).

fof(f102,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f96,f32])).

fof(f96,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f94,f34])).

fof(f94,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_1(sK5)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (11804)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11812)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (11811)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (11804)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11809)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (11817)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (11820)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(resolution,[],[f202,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    (~r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f9,f20,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK2,sK3,sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK2,sK3,sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) => (~r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f201,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v1_funct_1(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ~v1_funct_1(sK5) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f200,f176])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f146,f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    o_0_0_xboole_0 = sK2),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    o_0_0_xboole_0 != o_0_0_xboole_0 | o_0_0_xboole_0 = sK2),
% 0.21/0.53    inference(superposition,[],[f58,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    o_0_0_xboole_0 = sK3),
% 0.21/0.53    inference(resolution,[],[f139,f30])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~v1_funct_1(sK4) | o_0_0_xboole_0 = sK3),
% 0.21/0.53    inference(resolution,[],[f133,f32])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | o_0_0_xboole_0 = sK3),
% 0.21/0.53    inference(resolution,[],[f125,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_2(sK5,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ~v1_funct_2(sK5,sK2,sK3) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5) | o_0_0_xboole_0 = sK3),
% 0.21/0.53    inference(resolution,[],[f116,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  % (11800)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_2(sK5,sK2,X0) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5) | o_0_0_xboole_0 = X0) )),
% 0.21/0.53    inference(resolution,[],[f95,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f53,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK5,sK2,X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK5)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~v1_funct_2(sK5,sK2,X0) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f80,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f79,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r1_partfun1(sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~r1_partfun1(sK4,sK5) | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f78,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~r1_partfun1(sK4,sK5) | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f74,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(definition_folding,[],[f11,f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ~sP1(sK3,sK2,sK4) | ~v1_funct_1(sK5) | ~r1_partfun1(sK4,sK5) | ~v1_partfun1(sK5,sK2)),
% 0.21/0.53    inference(resolution,[],[f71,f34])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5) | ~r1_partfun1(sK4,sK5) | ~sP1(sK3,sK2,sK4)),
% 0.21/0.53    inference(resolution,[],[f68,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2,k5_partfun1(sK2,sK3,sK4)) | ~v1_partfun1(sK5,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK5) | ~r1_partfun1(X0,sK5)) )),
% 0.21/0.53    inference(resolution,[],[f62,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~r2_hidden(sK5,k5_partfun1(sK2,sK3,sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(equality_resolution,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK6(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X3))) | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK8(X0,X1,X2,X7)) & v1_partfun1(sK8(X0,X1,X2,X7),X1) & sK8(X0,X1,X2,X7) = X7 & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK6(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK6(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK6(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK8(X0,X1,X2,X7)) & v1_partfun1(sK8(X0,X1,X2,X7),X1) & sK8(X0,X1,X2,X7) = X7 & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X7))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.53    inference(rectify,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    o_0_0_xboole_0 != sK3 | o_0_0_xboole_0 = sK2),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f54,f54])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    v1_funct_2(sK5,sK2,o_0_0_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f33,f140])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ~v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5)),
% 0.21/0.53    inference(resolution,[],[f180,f182])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f147,f159])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,o_0_0_xboole_0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f34,f140])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) | ~v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5)),
% 0.21/0.53    inference(forward_demodulation,[],[f175,f159])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ~v1_funct_2(sK5,o_0_0_xboole_0,o_0_0_xboole_0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5)),
% 0.21/0.53    inference(backward_demodulation,[],[f117,f159])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK5,sK2,sK2) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5)),
% 0.21/0.53    inference(resolution,[],[f95,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f102,f30])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~v1_funct_1(sK4) | ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f96,f32])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f94,f34])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5) | ~v1_xboole_0(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f80,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11804)------------------------------
% 0.21/0.53  % (11804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11804)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11804)Memory used [KB]: 1918
% 0.21/0.53  % (11804)Time elapsed: 0.110 s
% 0.21/0.53  % (11804)------------------------------
% 0.21/0.53  % (11804)------------------------------
% 0.21/0.53  % (11797)Success in time 0.167 s
%------------------------------------------------------------------------------
