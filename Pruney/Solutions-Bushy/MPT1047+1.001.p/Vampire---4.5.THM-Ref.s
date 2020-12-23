%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1047+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 590 expanded)
%              Number of leaves         :   19 ( 185 expanded)
%              Depth                    :   21
%              Number of atoms          :  535 (3260 expanded)
%              Number of equality atoms :   82 ( 568 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2810,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2805,f220])).

fof(f220,plain,(
    sP3(k1_tarski(sK6),sK5,sK7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    inference(resolution,[],[f180,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP4(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP3(X2,X1,X0,X3) )
          & ( sP3(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP3(X1,X0,X2,X3) )
          & ( sP3(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP3(X1,X0,X2,X3) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f180,plain,(
    sP4(sK7,sK5,k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f166,f74])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK5,k1_tarski(sK6),sK7)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
          & v1_funct_2(X3,sK5,k1_tarski(sK6))
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK5,k1_tarski(sK6),sK7)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
        & v1_funct_2(X3,sK5,k1_tarski(sK6))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_2(sK8,sK5,k1_tarski(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f166,plain,
    ( sP4(sK7,sK5,k1_tarski(sK6))
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[],[f75,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP4(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f38,f49,f48,f47])).

fof(f47,plain,(
    ! [X2,X0,X4,X1] :
      ( sP2(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f48,plain,(
    ! [X1,X0,X2,X3] :
      ( sP3(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f75,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f2805,plain,(
    ~ sP3(k1_tarski(sK6),sK5,sK7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    inference(trivial_inequality_removal,[],[f2799])).

fof(f2799,plain,
    ( sK8 != sK8
    | ~ sP3(k1_tarski(sK6),sK5,sK7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    inference(superposition,[],[f522,f2763])).

fof(f2763,plain,(
    sK8 = sK10(sK8,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    inference(subsumption_resolution,[],[f2753,f220])).

fof(f2753,plain,
    ( sK8 = sK10(sK8,k5_partfun1(sK5,k1_tarski(sK6),sK7))
    | ~ sP3(k1_tarski(sK6),sK5,sK7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ),
    inference(resolution,[],[f2588,f599])).

fof(f599,plain,(
    ! [X0] :
      ( r2_hidden(sK10(sK8,X0),X0)
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f598,f513])).

fof(f513,plain,(
    ! [X0] :
      ( ~ sP0(sK8,X0)
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0) ) ),
    inference(superposition,[],[f509,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f3,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f509,plain,(
    ~ sP3(k1_tarski(sK6),sK5,sK7,k1_tarski(sK8)) ),
    inference(equality_resolution,[],[f488])).

fof(f488,plain,(
    ! [X0] :
      ( k1_tarski(sK8) != X0
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f217,f180])).

fof(f217,plain,(
    ! [X0] :
      ( k1_tarski(sK8) != X0
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0)
      | ~ sP4(sK7,sK5,k1_tarski(sK6)) ) ),
    inference(superposition,[],[f79,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X1,X2,X0) = X3
      | ~ sP3(X2,X1,X0,X3)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f79,plain,(
    k5_partfun1(sK5,k1_tarski(sK6),sK7) != k1_tarski(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f598,plain,(
    ! [X0] :
      ( ~ sP3(k1_tarski(sK6),sK5,sK7,X0)
      | sP0(sK8,X0)
      | r2_hidden(sK10(sK8,X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f597])).

fof(f597,plain,(
    ! [X0] :
      ( sK8 != sK8
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0)
      | sP0(sK8,X0)
      | r2_hidden(sK10(sK8,X0),X0) ) ),
    inference(superposition,[],[f522,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK10(X0,X1) = X0
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f2588,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k5_partfun1(sK5,k1_tarski(sK6),sK7))
      | sK8 = X7 ) ),
    inference(subsumption_resolution,[],[f2587,f302])).

fof(f302,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK5,k1_tarski(sK6),sK7))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ) ),
    inference(resolution,[],[f179,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X1,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
      | ~ sP1(X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
      | ~ sP1(X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f179,plain,(
    ! [X4] :
      ( sP1(k1_tarski(sK6),sK5,X4)
      | ~ r2_hidden(X4,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ) ),
    inference(subsumption_resolution,[],[f165,f74])).

fof(f165,plain,(
    ! [X4] :
      ( sP1(k1_tarski(sK6),sK5,X4)
      | ~ r2_hidden(X4,k5_partfun1(sK5,k1_tarski(sK6),sK7))
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f75,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X0,X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X1,X0,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f36,f45])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f2587,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | sK8 = X7
      | ~ r2_hidden(X7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ) ),
    inference(subsumption_resolution,[],[f2575,f301])).

fof(f301,plain,(
    ! [X1] :
      ( v1_funct_2(X1,sK5,k1_tarski(sK6))
      | ~ r2_hidden(X1,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ) ),
    inference(resolution,[],[f179,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2575,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X7,sK5,k1_tarski(sK6))
      | sK8 = X7
      | ~ r2_hidden(X7,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ) ),
    inference(resolution,[],[f682,f300])).

fof(f300,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ r2_hidden(X0,k5_partfun1(sK5,k1_tarski(sK6),sK7)) ) ),
    inference(resolution,[],[f179,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f682,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | sK8 = X0 ) ),
    inference(subsumption_resolution,[],[f681,f76])).

fof(f76,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f681,plain,(
    ! [X0] :
      ( sK8 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK8) ) ),
    inference(subsumption_resolution,[],[f680,f77])).

fof(f77,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f680,plain,(
    ! [X0] :
      ( sK8 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(sK8) ) ),
    inference(subsumption_resolution,[],[f679,f78])).

fof(f78,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f679,plain,(
    ! [X0] :
      ( sK8 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(sK8) ) ),
    inference(duplicate_literal_removal,[],[f675])).

fof(f675,plain,(
    ! [X0] :
      ( sK8 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(X0,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
      | ~ v1_funct_1(sK8) ) ),
    inference(resolution,[],[f190,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f190,plain,(
    ! [X5] :
      ( ~ r2_relset_1(sK5,k1_tarski(sK6),sK8,X5)
      | sK8 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ) ),
    inference(resolution,[],[f78,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f522,plain,(
    ! [X1] :
      ( sK8 != sK10(sK8,X1)
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X1) ) ),
    inference(subsumption_resolution,[],[f521,f380])).

fof(f380,plain,(
    ! [X0] :
      ( r2_hidden(sK8,X0)
      | ~ sP3(k1_tarski(sK6),sK5,sK7,X0) ) ),
    inference(resolution,[],[f361,f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP2(X2,X1,X5,X0)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
          & ( sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
            | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X2,X1,X5,X0) )
            & ( sP2(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f66,f67])).

fof(f67,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK11(X0,X1,X2,X3),X3) )
        & ( sP2(X2,X1,sK11(X0,X1,X2,X3),X0)
          | r2_hidden(sK11(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X2,X1,X5,X0) )
            & ( sP2(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP3(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X2,X0,X4,X1) )
            & ( sP2(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f361,plain,(
    sP2(sK7,sK5,sK8,k1_tarski(sK6)) ),
    inference(resolution,[],[f358,f284])).

fof(f284,plain,(
    r1_partfun1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f282,f78])).

fof(f282,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    | r1_partfun1(sK7,sK8) ),
    inference(resolution,[],[f173,f76])).

fof(f173,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | r1_partfun1(sK7,X0) ) ),
    inference(subsumption_resolution,[],[f159,f74])).

fof(f159,plain,(
    ! [X0] :
      ( r1_partfun1(sK7,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f75,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f358,plain,(
    ! [X7] :
      ( ~ r1_partfun1(X7,sK8)
      | sP2(X7,sK5,sK8,k1_tarski(sK6)) ) ),
    inference(subsumption_resolution,[],[f207,f204])).

fof(f204,plain,(
    v1_partfun1(sK8,sK5) ),
    inference(subsumption_resolution,[],[f203,f81])).

fof(f81,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f203,plain,
    ( v1_partfun1(sK8,sK5)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f202,f76])).

fof(f202,plain,
    ( v1_partfun1(sK8,sK5)
    | ~ v1_funct_1(sK8)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f186,f77])).

fof(f186,plain,
    ( v1_partfun1(sK8,sK5)
    | ~ v1_funct_2(sK8,sK5,k1_tarski(sK6))
    | ~ v1_funct_1(sK8)
    | v1_xboole_0(k1_tarski(sK6)) ),
    inference(resolution,[],[f78,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f207,plain,(
    ! [X7] :
      ( sP2(X7,sK5,sK8,k1_tarski(sK6))
      | ~ r1_partfun1(X7,sK8)
      | ~ v1_partfun1(sK8,sK5) ) ),
    inference(subsumption_resolution,[],[f192,f76])).

fof(f192,plain,(
    ! [X7] :
      ( sP2(X7,sK5,sK8,k1_tarski(sK6))
      | ~ r1_partfun1(X7,sK8)
      | ~ v1_partfun1(sK8,sK5)
      | ~ v1_funct_1(sK8) ) ),
    inference(resolution,[],[f78,f122])).

fof(f122,plain,(
    ! [X4,X0,X3,X1] :
      ( sP2(X0,X1,X4,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK12(X0,X1,X2,X3))
          & v1_partfun1(sK12(X0,X1,X2,X3),X1)
          & sK12(X0,X1,X2,X3) = X2
          & m1_subset_1(sK12(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK12(X0,X1,X2,X3)) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f70,f71])).

fof(f71,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK12(X0,X1,X2,X3))
        & v1_partfun1(sK12(X0,X1,X2,X3),X1)
        & sK12(X0,X1,X2,X3) = X2
        & m1_subset_1(sK12(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK12(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
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
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP2(X2,X0,X4,X1)
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
        | ~ sP2(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f521,plain,(
    ! [X1] :
      ( ~ sP3(k1_tarski(sK6),sK5,sK7,X1)
      | sK8 != sK10(sK8,X1)
      | ~ r2_hidden(sK8,X1) ) ),
    inference(inner_rewriting,[],[f519])).

fof(f519,plain,(
    ! [X1] :
      ( ~ sP3(k1_tarski(sK6),sK5,sK7,X1)
      | sK8 != sK10(sK8,X1)
      | ~ r2_hidden(sK10(sK8,X1),X1) ) ),
    inference(resolution,[],[f513,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK10(X0,X1) != X0
      | ~ r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f59])).

%------------------------------------------------------------------------------
