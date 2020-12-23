%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 573 expanded)
%              Number of leaves         :   10 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :  257 (3320 expanded)
%              Number of equality atoms :   23 ( 240 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f70])).

fof(f70,plain,(
    ~ v1_funct_2(sK6,sK3,sK4) ),
    inference(subsumption_resolution,[],[f62,f69])).

fof(f69,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(forward_demodulation,[],[f68,f55])).

fof(f55,plain,(
    sK6 = sK8(sK5,sK3,sK6,sK4) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
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

fof(f53,plain,(
    sP0(sK5,sK3,sK6,sK4) ),
    inference(subsumption_resolution,[],[f52,f50])).

fof(f50,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f49,f28])).

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

fof(f49,plain,
    ( sP2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f52,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X2,X1,X0,k5_partfun1(sK3,sK4,sK5))
      | sP0(X0,X1,sK6,X2) ) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
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

fof(f68,plain,(
    m1_subset_1(sK8(sK5,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f41,f53])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f31,f61])).

fof(f61,plain,(
    v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f58,f53])).

fof(f58,plain,
    ( v1_funct_1(sK6)
    | ~ sP0(sK5,sK3,sK6,sK4) ),
    inference(superposition,[],[f40,f55])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f31,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(subsumption_resolution,[],[f73,f61])).

fof(f73,plain,
    ( ~ v1_funct_1(sK6)
    | v1_funct_2(sK6,sK3,sK4) ),
    inference(subsumption_resolution,[],[f71,f60])).

fof(f60,plain,(
    v1_partfun1(sK6,sK3) ),
    inference(subsumption_resolution,[],[f57,f53])).

fof(f57,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ sP0(sK5,sK3,sK6,sK4) ),
    inference(superposition,[],[f43,f55])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK8(X0,X1,X2,X3),X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( ~ v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | v1_funct_2(sK6,sK3,sK4) ),
    inference(resolution,[],[f69,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

%------------------------------------------------------------------------------
