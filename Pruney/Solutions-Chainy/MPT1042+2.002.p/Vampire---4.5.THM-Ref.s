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
% DateTime   : Thu Dec  3 13:06:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 573 expanded)
%              Number of leaves         :   10 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  260 (3323 expanded)
%              Number of equality atoms :   23 ( 240 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75,f62])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f59,f54])).

fof(f54,plain,(
    sP0(sK5,sK3,sK6,sK4) ),
    inference(subsumption_resolution,[],[f53,f51])).

fof(f51,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f28,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(sK6,sK3,sK4)
      | ~ v1_funct_1(sK6) )
    & r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f6,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X3,X0,X1)
              | ~ v1_funct_1(X3) )
            & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
            | ~ v1_funct_2(X3,sK3,sK4)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          | ~ v1_funct_2(X3,sK3,sK4)
          | ~ v1_funct_1(X3) )
        & r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(sK6,sK3,sK4)
        | ~ v1_funct_1(sK6) )
      & r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f50,plain,
    ( sP2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f10,f13,f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f53,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X2,X1,X0,k5_partfun1(sK3,sK4,sK5))
      | sP0(X0,X1,sK6,X2) ) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X5,X3)
      | sP0(X2,X1,X5,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK7(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK7(X0,X1,X2,X3),X0)
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f22])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK7(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK7(X0,X1,X2,X3),X0)
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f59,plain,
    ( v1_funct_1(sK6)
    | ~ sP0(sK5,sK3,sK6,sK4) ),
    inference(superposition,[],[f41,f56])).

fof(f56,plain,(
    sK6 = sK8(sK5,sK3,sK6,sK4) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | sK8(X0,X1,X2,X3) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
          & v1_partfun1(sK8(X0,X1,X2,X3),X1)
          & sK8(X0,X1,X2,X3) = X2
          & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK8(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
        & v1_partfun1(sK8(X0,X1,X2,X3),X1)
        & sK8(X0,X1,X2,X3) = X2
        & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK8(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f74,f71])).

fof(f71,plain,(
    ~ v1_funct_2(sK6,sK3,sK4) ),
    inference(subsumption_resolution,[],[f63,f70])).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(forward_demodulation,[],[f69,f56])).

fof(f69,plain,(
    m1_subset_1(sK8(sK5,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f42,f54])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f31,f62])).

fof(f31,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,
    ( v1_funct_2(sK6,sK3,sK4)
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f72,f61])).

fof(f61,plain,(
    v1_partfun1(sK6,sK3) ),
    inference(subsumption_resolution,[],[f58,f54])).

fof(f58,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ sP0(sK5,sK3,sK6,sK4) ),
    inference(superposition,[],[f44,f56])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK8(X0,X1,X2,X3),X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( ~ v1_partfun1(sK6,sK3)
    | v1_funct_2(sK6,sK3,sK4)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29593)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (29585)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (29593)Refutation not found, incomplete strategy% (29593)------------------------------
% 0.21/0.48  % (29593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29593)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29593)Memory used [KB]: 10490
% 0.21/0.48  % (29593)Time elapsed: 0.003 s
% 0.21/0.48  % (29593)------------------------------
% 0.21/0.48  % (29593)------------------------------
% 0.21/0.48  % (29585)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v1_funct_1(sK6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    sP0(sK5,sK3,sK6,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sP2(sK5,sK3,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_1(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK6,sK3,sK4) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f6,f16,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & r2_hidden(X3,k5_partfun1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(X3,sK3,sK4) | ~v1_funct_1(X3)) & r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(X3,sK3,sK4) | ~v1_funct_1(X3)) & r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK6,sK3,sK4) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & r2_hidden(X3,k5_partfun1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & r2_hidden(X3,k5_partfun1(X0,X1,X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sP2(sK5,sK3,sK4) | ~v1_funct_1(sK5)),
% 0.21/0.48    inference(resolution,[],[f47,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(definition_folding,[],[f10,f13,f12,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    sP0(sK5,sK3,sK6,sK4) | ~sP2(sK5,sK3,sK4)),
% 0.21/0.48    inference(resolution,[],[f52,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X2,X1,X0,k5_partfun1(sK3,sK4,sK5)) | sP0(X0,X1,sK6,X2)) )),
% 0.21/0.48    inference(resolution,[],[f37,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (~r2_hidden(X5,X3) | sP0(X2,X1,X5,X0) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK7(X0,X1,X2,X3),X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK7(X0,X1,X2,X3),X0) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK7(X0,X1,X2,X3),X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK7(X0,X1,X2,X3),X0) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.48    inference(rectify,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v1_funct_1(sK6) | ~sP0(sK5,sK3,sK6,sK4)),
% 0.21/0.48    inference(superposition,[],[f41,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    sK6 = sK8(sK5,sK3,sK6,sK4)),
% 0.21/0.48    inference(resolution,[],[f54,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | sK8(X0,X1,X2,X3) = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK8(X0,X1,X2,X3) = X2 & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK8(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK8(X0,X1,X2,X3) = X2 & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK8(X0,X1,X2,X3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.48    inference(rectify,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK8(X0,X1,X2,X3)) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~v1_funct_1(sK6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.48    inference(forward_demodulation,[],[f69,f56])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    m1_subset_1(sK8(sK5,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.48    inference(resolution,[],[f42,f54])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~v1_funct_2(sK6,sK3,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f31,f62])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~v1_funct_2(sK6,sK3,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    v1_funct_2(sK6,sK3,sK4) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v1_partfun1(sK6,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f54])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v1_partfun1(sK6,sK3) | ~sP0(sK5,sK3,sK6,sK4)),
% 0.21/0.48    inference(superposition,[],[f44,f56])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v1_partfun1(sK8(X0,X1,X2,X3),X1) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_partfun1(sK6,sK3) | v1_funct_2(sK6,sK3,sK4) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(resolution,[],[f70,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (29585)------------------------------
% 0.21/0.48  % (29585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29585)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (29585)Memory used [KB]: 6140
% 0.21/0.48  % (29585)Time elapsed: 0.062 s
% 0.21/0.48  % (29585)------------------------------
% 0.21/0.48  % (29585)------------------------------
% 0.21/0.48  % (29581)Success in time 0.123 s
%------------------------------------------------------------------------------
