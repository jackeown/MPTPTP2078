%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 (5035 expanded)
%              Number of leaves         :   18 (1507 expanded)
%              Depth                    :   35
%              Number of atoms          :  493 (35146 expanded)
%              Number of equality atoms :   88 (7137 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(subsumption_resolution,[],[f293,f335])).

fof(f335,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f334,f284])).

fof(f284,plain,(
    ! [X0,X1] : sP2(k1_xboole_0,X0,X1) ),
    inference(backward_demodulation,[],[f271,f274])).

fof(f274,plain,(
    k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f258,f240])).

fof(f240,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f209,f213])).

fof(f213,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f209,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f209,plain,(
    ! [X0] : r1_tarski(sK4,X0) ),
    inference(resolution,[],[f208,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f208,plain,(
    ! [X0] : ~ r2_hidden(X0,sK4) ),
    inference(resolution,[],[f207,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK4)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f206,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f205,f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f205,plain,(
    v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f204,f127])).

fof(f127,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f124,f48])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
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

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(sK5,X0,X1) ) ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
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

fof(f204,plain,
    ( v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f203,f54])).

fof(f54,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f203,plain,
    ( r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    | v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f200,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f200,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK3,sK5,X0)
      | r2_hidden(sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f196,f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f196,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f195,f51])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f195,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | sP0(sK5,sK3,sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f193,f190])).

fof(f190,plain,
    ( v1_partfun1(sK6,sK3)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f189,f51])).

fof(f189,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f188,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f188,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
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

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK6,X0)
      | sP0(sK5,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f191,f49])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f90,f52])).

fof(f52,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_partfun1(X0,X4)
      | sP0(X0,X1,X4,X3)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f258,plain,
    ( k1_xboole_0 = sK6
    | ~ r1_tarski(k1_xboole_0,sK6) ),
    inference(forward_demodulation,[],[f257,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f257,plain,
    ( sK6 = k2_zfmisc_1(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK6) ),
    inference(forward_demodulation,[],[f256,f213])).

fof(f256,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(forward_demodulation,[],[f226,f87])).

fof(f226,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(backward_demodulation,[],[f117,f213])).

fof(f117,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(resolution,[],[f62,f95])).

fof(f95,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f271,plain,(
    ! [X0,X1] : sP2(sK6,X0,X1) ),
    inference(subsumption_resolution,[],[f137,f270])).

fof(f270,plain,(
    ! [X0] : r1_tarski(sK6,X0) ),
    inference(subsumption_resolution,[],[f263,f239])).

fof(f239,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f208,f213])).

fof(f263,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK6,X0),k1_xboole_0)
      | r1_tarski(sK6,X0) ) ),
    inference(forward_demodulation,[],[f233,f87])).

fof(f233,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK6,X0),k2_zfmisc_1(sK3,k1_xboole_0))
      | r1_tarski(sK6,X0) ) ),
    inference(backward_demodulation,[],[f157,f213])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK6,X0),k2_zfmisc_1(sK3,sK4))
      | r1_tarski(sK6,X0) ) ),
    inference(resolution,[],[f152,f85])).

fof(f152,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,sK6)
      | r2_hidden(sK7(X8,X9),k2_zfmisc_1(sK3,sK4))
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f122,f95])).

fof(f122,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK7(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f118,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f63,f64])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6,k2_zfmisc_1(X0,X1))
      | sP2(sK6,X0,X1) ) ),
    inference(resolution,[],[f125,f67])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | sP2(sK6,X2,X3) ) ),
    inference(resolution,[],[f83,f49])).

fof(f334,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))
      | ~ sP2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f327,f89])).

fof(f327,plain,(
    ! [X2,X1] :
      ( ~ sP1(X2,k1_xboole_0,k1_xboole_0,X1)
      | r2_hidden(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f325,f74])).

fof(f325,plain,(
    ! [X0] : sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f324,f100])).

fof(f100,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f92,f98])).

fof(f98,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f56,f87])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f323,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f323,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f294,f103])).

fof(f103,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f55,f98])).

fof(f55,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f294,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(k1_xboole_0,X0,k1_xboole_0,X1) ) ),
    inference(backward_demodulation,[],[f286,f273])).

fof(f273,plain,(
    k1_xboole_0 = sK5 ),
    inference(subsumption_resolution,[],[f255,f240])).

fof(f255,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k1_xboole_0,sK5) ),
    inference(forward_demodulation,[],[f254,f87])).

fof(f254,plain,
    ( sK5 = k2_zfmisc_1(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5) ),
    inference(forward_demodulation,[],[f253,f213])).

fof(f253,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(forward_demodulation,[],[f225,f87])).

fof(f225,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f116,f213])).

fof(f116,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f66,f48])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(sK5,X0,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f285,f274])).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(sK5,X0,k1_xboole_0,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f277,f274])).

fof(f277,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,k1_xboole_0,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f193,f274])).

fof(f293,plain,(
    ~ r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f280,f273])).

fof(f280,plain,(
    ~ r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f250,f274])).

fof(f250,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5)) ),
    inference(forward_demodulation,[],[f222,f218])).

fof(f218,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f53,f213])).

fof(f53,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f222,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f54,f213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (20473)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (20464)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (20466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20480)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (20465)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20484)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (20476)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (20483)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (20463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (20469)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (20472)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20467)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (20474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (20475)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (20484)Refutation not found, incomplete strategy% (20484)------------------------------
% 0.21/0.53  % (20484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20484)Memory used [KB]: 10874
% 0.21/0.53  % (20484)Time elapsed: 0.085 s
% 0.21/0.53  % (20484)------------------------------
% 0.21/0.53  % (20484)------------------------------
% 0.21/0.53  % (20490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (20491)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (20482)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20486)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (20478)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (20462)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (20488)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (20479)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (20481)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (20470)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (20489)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (20468)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (20485)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (20477)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (20469)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f336,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f293,f335])).
% 0.21/0.56  fof(f335,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f334,f284])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(k1_xboole_0,X0,X1)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f271,f274])).
% 0.21/0.56  fof(f274,plain,(
% 0.21/0.56    k1_xboole_0 = sK6),
% 0.21/0.56    inference(subsumption_resolution,[],[f258,f240])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f209,f213])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    k1_xboole_0 = sK4),
% 0.21/0.56    inference(resolution,[],[f209,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(sK4,X0)) )),
% 0.21/0.56    inference(resolution,[],[f208,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK4)) )),
% 0.21/0.56    inference(resolution,[],[f207,f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,sK4) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f206,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK4)) | ~r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f205,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    v1_xboole_0(sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f204,f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    sP2(sK5,sK3,sK4)),
% 0.21/0.56    inference(resolution,[],[f124,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f26,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(sK5,X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f83,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    v1_funct_1(sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(definition_folding,[],[f19,f23,f22,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f203,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) | v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.21/0.56    inference(resolution,[],[f200,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f23])).
% 0.21/0.56  fof(f200,plain,(
% 0.21/0.56    ( ! [X0] : (~sP1(sK4,sK3,sK5,X0) | r2_hidden(sK6,X0) | v1_xboole_0(sK4)) )),
% 0.21/0.56    inference(resolution,[],[f196,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X5,X3,X1] : (~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK8(X0,X1,X2,X3),X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.56    inference(rectify,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 0.21/0.56    inference(nnf_transformation,[],[f22])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    sP0(sK5,sK3,sK6,sK4) | v1_xboole_0(sK4)),
% 0.21/0.56    inference(resolution,[],[f195,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | sP0(sK5,sK3,sK6,X0) | v1_xboole_0(sK4)) )),
% 0.21/0.56    inference(resolution,[],[f193,f190])).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    v1_partfun1(sK6,sK3) | v1_xboole_0(sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f189,f51])).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    v1_partfun1(sK6,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f188,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    v1_funct_1(sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    v1_partfun1(sK6,sK3) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.21/0.56    inference(resolution,[],[f59,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_partfun1(sK6,X0) | sP0(sK5,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f191,f49])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP0(sK5,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK6)) )),
% 0.21/0.56    inference(resolution,[],[f90,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    r1_partfun1(sK5,sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X4,X0,X3,X1] : (~r1_partfun1(X0,X4) | sP0(X0,X1,X4,X3) | ~v1_partfun1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.56    inference(equality_resolution,[],[f82])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK9(X0,X1,X2,X3)) & v1_partfun1(sK9(X0,X1,X2,X3),X1) & sK9(X0,X1,X2,X3) = X2 & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK9(X0,X1,X2,X3))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.56    inference(rectify,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f21])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    k1_xboole_0 = sK6 | ~r1_tarski(k1_xboole_0,sK6)),
% 0.21/0.56    inference(forward_demodulation,[],[f257,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.56    inference(flattening,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.56  fof(f257,plain,(
% 0.21/0.56    sK6 = k2_zfmisc_1(sK3,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK6)),
% 0.21/0.56    inference(forward_demodulation,[],[f256,f213])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.21/0.56    inference(forward_demodulation,[],[f226,f87])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.21/0.56    inference(backward_demodulation,[],[f117,f213])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.21/0.56    inference(resolution,[],[f62,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))),
% 0.21/0.56    inference(resolution,[],[f66,f51])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f271,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(sK6,X0,X1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f137,f270])).
% 0.21/0.56  fof(f270,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(sK6,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f263,f239])).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f208,f213])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(sK6,X0),k1_xboole_0) | r1_tarski(sK6,X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f233,f87])).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(sK6,X0),k2_zfmisc_1(sK3,k1_xboole_0)) | r1_tarski(sK6,X0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f157,f213])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(sK6,X0),k2_zfmisc_1(sK3,sK4)) | r1_tarski(sK6,X0)) )),
% 0.21/0.56    inference(resolution,[],[f152,f85])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    ( ! [X8,X9] : (~r1_tarski(X8,sK6) | r2_hidden(sK7(X8,X9),k2_zfmisc_1(sK3,sK4)) | r1_tarski(X8,X9)) )),
% 0.21/0.56    inference(resolution,[],[f122,f95])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK7(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 0.21/0.56    inference(resolution,[],[f118,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f63,f64])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(sK6,k2_zfmisc_1(X0,X1)) | sP2(sK6,X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f125,f67])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | sP2(sK6,X2,X3)) )),
% 0.21/0.56    inference(resolution,[],[f83,f49])).
% 0.21/0.56  fof(f334,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) | ~sP2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f327,f89])).
% 0.21/0.56  fof(f327,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~sP1(X2,k1_xboole_0,k1_xboole_0,X1) | r2_hidden(k1_xboole_0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f325,f74])).
% 0.21/0.56  fof(f325,plain,(
% 0.21/0.56    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f324,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.56    inference(backward_demodulation,[],[f92,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f97,f57])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f66,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.56    inference(superposition,[],[f56,f87])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.56  fof(f324,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f323,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f294,f103])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f55,f98])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(k1_xboole_0,X0,k1_xboole_0,X1)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f286,f273])).
% 0.21/0.56  fof(f273,plain,(
% 0.21/0.56    k1_xboole_0 = sK5),
% 0.21/0.56    inference(subsumption_resolution,[],[f255,f240])).
% 0.21/0.56  fof(f255,plain,(
% 0.21/0.56    k1_xboole_0 = sK5 | ~r1_tarski(k1_xboole_0,sK5)),
% 0.21/0.56    inference(forward_demodulation,[],[f254,f87])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    sK5 = k2_zfmisc_1(sK3,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK5)),
% 0.21/0.56    inference(forward_demodulation,[],[f253,f213])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.21/0.56    inference(forward_demodulation,[],[f225,f87])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.21/0.56    inference(backward_demodulation,[],[f116,f213])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.21/0.56    inference(resolution,[],[f62,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))),
% 0.21/0.56    inference(resolution,[],[f66,f48])).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(k1_xboole_0,X0) | sP0(sK5,X0,k1_xboole_0,X1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f285,f274])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(sK5,X0,k1_xboole_0,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f277,f274])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP0(sK5,X0,k1_xboole_0,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(backward_demodulation,[],[f193,f274])).
% 0.21/0.56  fof(f293,plain,(
% 0.21/0.56    ~r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.56    inference(backward_demodulation,[],[f280,f273])).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    ~r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5))),
% 0.21/0.56    inference(backward_demodulation,[],[f250,f274])).
% 0.21/0.56  fof(f250,plain,(
% 0.21/0.56    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5))),
% 0.21/0.56    inference(forward_demodulation,[],[f222,f218])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    k1_xboole_0 = sK3),
% 0.21/0.56    inference(subsumption_resolution,[],[f53,f213])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    k1_xboole_0 != sK4 | k1_xboole_0 = sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    ~r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5))),
% 0.21/0.56    inference(backward_demodulation,[],[f54,f213])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20469)------------------------------
% 0.21/0.56  % (20469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20469)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20469)Memory used [KB]: 6396
% 0.21/0.56  % (20469)Time elapsed: 0.150 s
% 0.21/0.56  % (20469)------------------------------
% 0.21/0.56  % (20469)------------------------------
% 0.21/0.56  % (20461)Success in time 0.205 s
%------------------------------------------------------------------------------
