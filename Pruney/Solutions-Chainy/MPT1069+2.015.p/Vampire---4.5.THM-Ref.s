%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 469 expanded)
%              Number of leaves         :   25 ( 184 expanded)
%              Depth                    :   31
%              Number of atoms          :  612 (3931 expanded)
%              Number of equality atoms :  112 ( 883 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f489,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f76,f74,f472,f201])).

fof(f201,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f130,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f93,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
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

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f91,f125])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f472,plain,(
    v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f427,f76])).

fof(f427,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(superposition,[],[f66,f425])).

fof(f425,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f424,f166])).

fof(f166,plain,
    ( ~ v1_xboole_0(sK5)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f161,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X1,X0)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f161,plain,
    ( sP0(sK4,sK3,sK5)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f160,f66])).

fof(f160,plain,
    ( sP0(sK4,sK3,sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK3
                & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                & m1_subset_1(X5,sK3) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(sK5,X5))
              & k1_xboole_0 != sK3
              & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,X4))
              & m1_subset_1(X5,sK3) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(sK5,X5))
            & k1_xboole_0 != sK3
            & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,X4))
            & m1_subset_1(X5,sK3) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X5) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,X5))
          & k1_xboole_0 != sK3
          & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
          & m1_subset_1(X5,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X5) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,X5))
        & k1_xboole_0 != sK3
        & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
        & m1_subset_1(X5,sK3) )
   => ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
      & k1_xboole_0 != sK3
      & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
      & m1_subset_1(sK7,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f159,plain,
    ( ~ v1_funct_1(sK5)
    | sP0(sK4,sK3,sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f153,f68])).

fof(f68,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f153,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | sP0(sK4,sK3,sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f87,f69])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP0(X1,X0,X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP0(X1,X0,X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f29,f41])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f424,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f418,f122])).

fof(f122,plain,
    ( r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f83,f72])).

fof(f72,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f418,plain,
    ( ~ r2_hidden(sK7,sK3)
    | k1_xboole_0 = sK4
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f417,f76])).

fof(f417,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK5)
    | k1_xboole_0 = sK4
    | ~ r2_hidden(sK7,sK3) ),
    inference(forward_demodulation,[],[f415,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f415,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0))
    | v1_xboole_0(sK5)
    | k1_xboole_0 = sK4
    | ~ r2_hidden(sK7,sK3) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0))
    | v1_xboole_0(sK5)
    | k1_xboole_0 = sK4
    | ~ r2_hidden(sK7,sK3)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f227,f397])).

fof(f397,plain,
    ( k1_xboole_0 = k1_relat_1(sK6)
    | ~ r2_hidden(sK7,sK3)
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f240,f221])).

fof(f221,plain,
    ( sP1(k1_relat_1(sK6),sK3,sK5)
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f188,f149])).

fof(f149,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f148,f71])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f148,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(superposition,[],[f73,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f188,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),X4)
      | k1_xboole_0 = sK4
      | sP1(X4,sK3,sK5) ) ),
    inference(subsumption_resolution,[],[f187,f67])).

fof(f187,plain,(
    ! [X4] :
      ( k1_xboole_0 = sK4
      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),X4)
      | sP1(X4,sK3,sK5)
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f181,f68])).

fof(f181,plain,(
    ! [X4] :
      ( k1_xboole_0 = sK4
      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),X4)
      | sP1(X4,sK3,sK5)
      | ~ v1_funct_2(sK5,sK3,sK4)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f105,f69])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | sP1(X2,X0,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X2,X0,X3)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f40,f43])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP1(X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f240,plain,(
    ! [X10] :
      ( ~ sP1(k1_relat_1(sK6),X10,sK5)
      | k1_xboole_0 = k1_relat_1(sK6)
      | ~ r2_hidden(sK7,X10) ) ),
    inference(resolution,[],[f176,f219])).

fof(f219,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f218,f119])).

fof(f119,plain,(
    v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f117,f82])).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,
    ( v1_relat_1(sK6)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
    inference(resolution,[],[f77,f71])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f218,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f217,f136])).

fof(f136,plain,(
    v5_relat_1(sK6,sK2) ),
    inference(resolution,[],[f100,f71])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f217,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6))
    | ~ v5_relat_1(sK6,sK2)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f216,f70])).

fof(f70,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f216,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v5_relat_1(sK6,sK2)
    | ~ v1_relat_1(sK6) ),
    inference(trivial_inequality_removal,[],[f215])).

fof(f215,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v5_relat_1(sK6,sK2)
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f199,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f199,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(subsumption_resolution,[],[f198,f66])).

fof(f198,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f197,f67])).

fof(f197,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f196,f68])).

fof(f196,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f195,f69])).

fof(f195,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f194,f70])).

fof(f194,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f193,f71])).

fof(f193,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f192,f72])).

fof(f192,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ m1_subset_1(sK7,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f191,f73])).

fof(f191,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    | ~ m1_subset_1(sK7,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f190,f74])).

fof(f190,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    | ~ m1_subset_1(sK7,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4) ),
    inference(superposition,[],[f75,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f75,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f49])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ sP1(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f175,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP1(X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ sP1(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f170,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ v1_funct_1(X3)
      | ~ sP1(X0,X2,X3) ) ),
    inference(resolution,[],[f101,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f227,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6)))
    | v1_xboole_0(sK5)
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f221,f140])).

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | v1_xboole_0(X5)
      | ~ v1_xboole_0(k2_zfmisc_1(X4,X3)) ) ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f66,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31022)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (31020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (31023)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (31012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (31015)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (31004)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (31014)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (31005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (31009)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31007)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (30998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (31000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31021)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (31020)Refutation not found, incomplete strategy% (31020)------------------------------
% 0.20/0.53  % (31020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31020)Memory used [KB]: 11001
% 0.20/0.53  % (31020)Time elapsed: 0.082 s
% 0.20/0.53  % (31020)------------------------------
% 0.20/0.53  % (31020)------------------------------
% 0.20/0.54  % (31016)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (31018)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (31013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (31001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (31002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (31003)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (31015)Refutation not found, incomplete strategy% (31015)------------------------------
% 0.20/0.54  % (31015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31015)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31015)Memory used [KB]: 10746
% 0.20/0.54  % (31015)Time elapsed: 0.119 s
% 0.20/0.54  % (31015)------------------------------
% 0.20/0.54  % (31015)------------------------------
% 0.20/0.55  % (31008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (31027)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (31006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (31026)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (31025)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (31019)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (31017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (31024)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.58  % (31027)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 1.71/0.60  % SZS output start Proof for theBenchmark
% 1.71/0.60  fof(f489,plain,(
% 1.71/0.60    $false),
% 1.71/0.60    inference(unit_resulting_resolution,[],[f76,f74,f472,f201])).
% 1.71/0.60  fof(f201,plain,(
% 1.71/0.60    ( ! [X2,X1] : (X1 = X2 | ~v1_xboole_0(X2) | ~v1_xboole_0(X1)) )),
% 1.71/0.60    inference(resolution,[],[f130,f125])).
% 1.71/0.60  fof(f125,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.71/0.60    inference(resolution,[],[f93,f80])).
% 1.71/0.60  fof(f80,plain,(
% 1.71/0.60    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f53])).
% 1.71/0.60  fof(f53,plain,(
% 1.71/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.71/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 1.71/0.60  fof(f52,plain,(
% 1.71/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f51,plain,(
% 1.71/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.71/0.60    inference(rectify,[],[f50])).
% 1.71/0.60  fof(f50,plain,(
% 1.71/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.71/0.60    inference(nnf_transformation,[],[f1])).
% 1.71/0.60  fof(f1,axiom,(
% 1.71/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.71/0.60  fof(f93,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f61])).
% 1.71/0.60  fof(f61,plain,(
% 1.71/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).
% 1.71/0.60  fof(f60,plain,(
% 1.71/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f59,plain,(
% 1.71/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.60    inference(rectify,[],[f58])).
% 1.71/0.60  fof(f58,plain,(
% 1.71/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.60    inference(nnf_transformation,[],[f32])).
% 1.71/0.60  fof(f32,plain,(
% 1.71/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.71/0.60    inference(ennf_transformation,[],[f2])).
% 1.71/0.60  fof(f2,axiom,(
% 1.71/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.71/0.60  fof(f130,plain,(
% 1.71/0.60    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 1.71/0.60    inference(resolution,[],[f91,f125])).
% 1.71/0.60  fof(f91,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f57])).
% 1.71/0.60  fof(f57,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(flattening,[],[f56])).
% 1.71/0.60  fof(f56,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f4])).
% 1.71/0.60  fof(f4,axiom,(
% 1.71/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.60  fof(f472,plain,(
% 1.71/0.60    v1_xboole_0(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f427,f76])).
% 1.71/0.60  fof(f427,plain,(
% 1.71/0.60    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(superposition,[],[f66,f425])).
% 1.71/0.60  fof(f425,plain,(
% 1.71/0.60    k1_xboole_0 = sK4 | v1_xboole_0(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f424,f166])).
% 1.71/0.60  fof(f166,plain,(
% 1.71/0.60    ~v1_xboole_0(sK5) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(resolution,[],[f161,f85])).
% 1.71/0.60  fof(f85,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_xboole_0(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f55])).
% 1.71/0.60  fof(f55,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((v1_funct_2(X2,X1,X0) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP0(X0,X1,X2))),
% 1.71/0.60    inference(rectify,[],[f54])).
% 1.71/0.60  fof(f54,plain,(
% 1.71/0.60    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.71/0.60    inference(nnf_transformation,[],[f41])).
% 1.71/0.60  fof(f41,plain,(
% 1.71/0.60    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 1.71/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.71/0.60  fof(f161,plain,(
% 1.71/0.60    sP0(sK4,sK3,sK5) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f160,f66])).
% 1.71/0.60  fof(f160,plain,(
% 1.71/0.60    sP0(sK4,sK3,sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f159,f67])).
% 1.71/0.60  fof(f67,plain,(
% 1.71/0.60    v1_funct_1(sK5)),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f49,plain,(
% 1.71/0.60    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 1.71/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f48,f47,f46,f45])).
% 1.71/0.60  fof(f45,plain,(
% 1.71/0.60    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f46,plain,(
% 1.71/0.60    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f47,plain,(
% 1.71/0.60    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X5) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(X5,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f48,plain,(
% 1.71/0.60    ? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X5) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(X5,sK3)) => (k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3))),
% 1.71/0.60    introduced(choice_axiom,[])).
% 1.71/0.60  fof(f22,plain,(
% 1.71/0.60    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.71/0.60    inference(flattening,[],[f21])).
% 1.71/0.60  fof(f21,plain,(
% 1.71/0.60    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.71/0.60    inference(ennf_transformation,[],[f19])).
% 1.71/0.60  fof(f19,negated_conjecture,(
% 1.71/0.60    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.71/0.60    inference(negated_conjecture,[],[f18])).
% 1.71/0.60  fof(f18,conjecture,(
% 1.71/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.71/0.60  fof(f159,plain,(
% 1.71/0.60    ~v1_funct_1(sK5) | sP0(sK4,sK3,sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(subsumption_resolution,[],[f153,f68])).
% 1.71/0.60  fof(f68,plain,(
% 1.71/0.60    v1_funct_2(sK5,sK3,sK4)),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f153,plain,(
% 1.71/0.60    ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | sP0(sK4,sK3,sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(resolution,[],[f87,f69])).
% 1.71/0.60  fof(f69,plain,(
% 1.71/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f87,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP0(X1,X0,X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f42])).
% 1.71/0.60  fof(f42,plain,(
% 1.71/0.60    ! [X0,X1] : (! [X2] : (sP0(X1,X0,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.71/0.60    inference(definition_folding,[],[f29,f41])).
% 1.71/0.60  fof(f29,plain,(
% 1.71/0.60    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.71/0.60    inference(flattening,[],[f28])).
% 1.71/0.60  fof(f28,plain,(
% 1.71/0.60    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.71/0.60    inference(ennf_transformation,[],[f13])).
% 1.71/0.60  fof(f13,axiom,(
% 1.71/0.60    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 1.71/0.60  fof(f424,plain,(
% 1.71/0.60    k1_xboole_0 = sK4 | v1_xboole_0(sK5) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(resolution,[],[f418,f122])).
% 1.71/0.60  fof(f122,plain,(
% 1.71/0.60    r2_hidden(sK7,sK3) | v1_xboole_0(sK3)),
% 1.71/0.60    inference(resolution,[],[f83,f72])).
% 1.71/0.60  fof(f72,plain,(
% 1.71/0.60    m1_subset_1(sK7,sK3)),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f83,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f27])).
% 1.71/0.60  fof(f27,plain,(
% 1.71/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.71/0.60    inference(flattening,[],[f26])).
% 1.71/0.60  fof(f26,plain,(
% 1.71/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f7])).
% 1.71/0.60  fof(f7,axiom,(
% 1.71/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.71/0.60  fof(f418,plain,(
% 1.71/0.60    ~r2_hidden(sK7,sK3) | k1_xboole_0 = sK4 | v1_xboole_0(sK5)),
% 1.71/0.60    inference(subsumption_resolution,[],[f417,f76])).
% 1.71/0.60  fof(f417,plain,(
% 1.71/0.60    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK5) | k1_xboole_0 = sK4 | ~r2_hidden(sK7,sK3)),
% 1.71/0.60    inference(forward_demodulation,[],[f415,f109])).
% 1.71/0.60  fof(f109,plain,(
% 1.71/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.71/0.60    inference(equality_resolution,[],[f97])).
% 1.71/0.60  fof(f97,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.71/0.60    inference(cnf_transformation,[],[f63])).
% 1.71/0.60  fof(f63,plain,(
% 1.71/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.60    inference(flattening,[],[f62])).
% 1.71/0.60  fof(f62,plain,(
% 1.71/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.60    inference(nnf_transformation,[],[f5])).
% 1.71/0.60  fof(f5,axiom,(
% 1.71/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.60  fof(f415,plain,(
% 1.71/0.60    ~v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) | v1_xboole_0(sK5) | k1_xboole_0 = sK4 | ~r2_hidden(sK7,sK3)),
% 1.71/0.60    inference(duplicate_literal_removal,[],[f405])).
% 1.71/0.60  fof(f405,plain,(
% 1.71/0.60    ~v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) | v1_xboole_0(sK5) | k1_xboole_0 = sK4 | ~r2_hidden(sK7,sK3) | k1_xboole_0 = sK4),
% 1.71/0.60    inference(superposition,[],[f227,f397])).
% 1.71/0.60  fof(f397,plain,(
% 1.71/0.60    k1_xboole_0 = k1_relat_1(sK6) | ~r2_hidden(sK7,sK3) | k1_xboole_0 = sK4),
% 1.71/0.60    inference(resolution,[],[f240,f221])).
% 1.71/0.60  fof(f221,plain,(
% 1.71/0.60    sP1(k1_relat_1(sK6),sK3,sK5) | k1_xboole_0 = sK4),
% 1.71/0.60    inference(resolution,[],[f188,f149])).
% 1.71/0.60  fof(f149,plain,(
% 1.71/0.60    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6))),
% 1.71/0.60    inference(subsumption_resolution,[],[f148,f71])).
% 1.71/0.60  fof(f71,plain,(
% 1.71/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f148,plain,(
% 1.71/0.60    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 1.71/0.60    inference(superposition,[],[f73,f99])).
% 1.71/0.60  fof(f99,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f35])).
% 1.71/0.60  fof(f35,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f12])).
% 1.71/0.60  fof(f12,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.60  fof(f73,plain,(
% 1.71/0.60    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f188,plain,(
% 1.71/0.60    ( ! [X4] : (~r1_tarski(k2_relset_1(sK3,sK4,sK5),X4) | k1_xboole_0 = sK4 | sP1(X4,sK3,sK5)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f187,f67])).
% 1.71/0.60  fof(f187,plain,(
% 1.71/0.60    ( ! [X4] : (k1_xboole_0 = sK4 | ~r1_tarski(k2_relset_1(sK3,sK4,sK5),X4) | sP1(X4,sK3,sK5) | ~v1_funct_1(sK5)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f181,f68])).
% 1.71/0.60  fof(f181,plain,(
% 1.71/0.60    ( ! [X4] : (k1_xboole_0 = sK4 | ~r1_tarski(k2_relset_1(sK3,sK4,sK5),X4) | sP1(X4,sK3,sK5) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) )),
% 1.71/0.60    inference(resolution,[],[f105,f69])).
% 1.71/0.60  fof(f105,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | sP1(X2,X0,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f44])).
% 1.71/0.60  fof(f44,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (sP1(X2,X0,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.60    inference(definition_folding,[],[f40,f43])).
% 1.71/0.60  fof(f43,plain,(
% 1.71/0.60    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP1(X2,X0,X3))),
% 1.71/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.71/0.60  fof(f40,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.60    inference(flattening,[],[f39])).
% 1.71/0.60  fof(f39,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.71/0.60    inference(ennf_transformation,[],[f17])).
% 1.71/0.60  fof(f17,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.71/0.60  fof(f240,plain,(
% 1.71/0.60    ( ! [X10] : (~sP1(k1_relat_1(sK6),X10,sK5) | k1_xboole_0 = k1_relat_1(sK6) | ~r2_hidden(sK7,X10)) )),
% 1.71/0.60    inference(resolution,[],[f176,f219])).
% 1.71/0.60  fof(f219,plain,(
% 1.71/0.60    ~r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6))),
% 1.71/0.60    inference(subsumption_resolution,[],[f218,f119])).
% 1.71/0.60  fof(f119,plain,(
% 1.71/0.60    v1_relat_1(sK6)),
% 1.71/0.60    inference(subsumption_resolution,[],[f117,f82])).
% 1.71/0.60  fof(f82,plain,(
% 1.71/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f9])).
% 1.71/0.60  fof(f9,axiom,(
% 1.71/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.60  fof(f117,plain,(
% 1.71/0.60    v1_relat_1(sK6) | ~v1_relat_1(k2_zfmisc_1(sK4,sK2))),
% 1.71/0.60    inference(resolution,[],[f77,f71])).
% 1.71/0.60  fof(f77,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f23])).
% 1.71/0.60  fof(f23,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f8])).
% 1.71/0.60  fof(f8,axiom,(
% 1.71/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.60  fof(f218,plain,(
% 1.71/0.60    ~r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6)) | ~v1_relat_1(sK6)),
% 1.71/0.60    inference(subsumption_resolution,[],[f217,f136])).
% 1.71/0.60  fof(f136,plain,(
% 1.71/0.60    v5_relat_1(sK6,sK2)),
% 1.71/0.60    inference(resolution,[],[f100,f71])).
% 1.71/0.60  fof(f100,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f36])).
% 1.71/0.60  fof(f36,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.60    inference(ennf_transformation,[],[f20])).
% 1.71/0.60  fof(f20,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.71/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.71/0.60  fof(f11,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.60  fof(f217,plain,(
% 1.71/0.60    ~r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6)) | ~v5_relat_1(sK6,sK2) | ~v1_relat_1(sK6)),
% 1.71/0.60    inference(subsumption_resolution,[],[f216,f70])).
% 1.71/0.60  fof(f70,plain,(
% 1.71/0.60    v1_funct_1(sK6)),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f216,plain,(
% 1.71/0.60    ~r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v5_relat_1(sK6,sK2) | ~v1_relat_1(sK6)),
% 1.71/0.60    inference(trivial_inequality_removal,[],[f215])).
% 1.71/0.60  fof(f215,plain,(
% 1.71/0.60    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~r2_hidden(k1_funct_1(sK5,sK7),k1_relat_1(sK6)) | ~v1_funct_1(sK6) | ~v5_relat_1(sK6,sK2) | ~v1_relat_1(sK6)),
% 1.71/0.60    inference(superposition,[],[f199,f88])).
% 1.71/0.60  fof(f88,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f31])).
% 1.71/0.60  fof(f31,plain,(
% 1.71/0.60    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(flattening,[],[f30])).
% 1.71/0.60  fof(f30,plain,(
% 1.71/0.60    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.71/0.60    inference(ennf_transformation,[],[f14])).
% 1.71/0.60  fof(f14,axiom,(
% 1.71/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.71/0.60  fof(f199,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))),
% 1.71/0.60    inference(subsumption_resolution,[],[f198,f66])).
% 1.71/0.60  fof(f198,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f197,f67])).
% 1.71/0.60  fof(f197,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f196,f68])).
% 1.71/0.60  fof(f196,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f195,f69])).
% 1.71/0.60  fof(f195,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f194,f70])).
% 1.71/0.60  fof(f194,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f193,f71])).
% 1.71/0.60  fof(f193,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f192,f72])).
% 1.71/0.60  fof(f192,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~m1_subset_1(sK7,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f191,f73])).
% 1.71/0.60  fof(f191,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | ~r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) | ~m1_subset_1(sK7,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(subsumption_resolution,[],[f190,f74])).
% 1.71/0.60  fof(f190,plain,(
% 1.71/0.60    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) | k1_xboole_0 = sK3 | ~r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) | ~m1_subset_1(sK7,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5) | v1_xboole_0(sK4)),
% 1.71/0.60    inference(superposition,[],[f75,f98])).
% 1.71/0.60  fof(f98,plain,(
% 1.71/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f34])).
% 1.71/0.60  fof(f34,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.71/0.60    inference(flattening,[],[f33])).
% 1.71/0.60  fof(f33,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.71/0.60    inference(ennf_transformation,[],[f15])).
% 1.71/0.60  fof(f15,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.71/0.60  fof(f75,plain,(
% 1.71/0.60    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f176,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X1),X0) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~sP1(X0,X2,X3)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f175,f103])).
% 1.71/0.60  fof(f103,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | v1_funct_2(X2,X1,X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f65])).
% 1.71/0.60  fof(f65,plain,(
% 1.71/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP1(X0,X1,X2))),
% 1.71/0.60    inference(rectify,[],[f64])).
% 1.71/0.60  fof(f64,plain,(
% 1.71/0.60    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP1(X2,X0,X3))),
% 1.71/0.60    inference(nnf_transformation,[],[f43])).
% 1.71/0.60  fof(f175,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~sP1(X0,X2,X3)) )),
% 1.71/0.60    inference(subsumption_resolution,[],[f170,f102])).
% 1.71/0.60  fof(f102,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | v1_funct_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f65])).
% 1.71/0.60  fof(f170,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~sP1(X0,X2,X3)) )),
% 1.71/0.60    inference(resolution,[],[f101,f104])).
% 1.71/0.60  fof(f104,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP1(X0,X1,X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f65])).
% 1.71/0.60  fof(f101,plain,(
% 1.71/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f38])).
% 1.71/0.60  fof(f38,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.60    inference(flattening,[],[f37])).
% 1.71/0.60  fof(f37,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.71/0.60    inference(ennf_transformation,[],[f16])).
% 1.71/0.60  fof(f16,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.71/0.60  fof(f227,plain,(
% 1.71/0.60    ~v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) | v1_xboole_0(sK5) | k1_xboole_0 = sK4),
% 1.71/0.60    inference(resolution,[],[f221,f140])).
% 1.71/0.60  fof(f140,plain,(
% 1.71/0.60    ( ! [X4,X5,X3] : (~sP1(X3,X4,X5) | v1_xboole_0(X5) | ~v1_xboole_0(k2_zfmisc_1(X4,X3))) )),
% 1.71/0.60    inference(resolution,[],[f104,f79])).
% 1.71/0.60  fof(f79,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f25])).
% 1.71/0.60  fof(f25,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f6])).
% 1.71/0.60  fof(f6,axiom,(
% 1.71/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.71/0.60  fof(f66,plain,(
% 1.71/0.60    ~v1_xboole_0(sK4)),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f74,plain,(
% 1.71/0.60    k1_xboole_0 != sK3),
% 1.71/0.60    inference(cnf_transformation,[],[f49])).
% 1.71/0.60  fof(f76,plain,(
% 1.71/0.60    v1_xboole_0(k1_xboole_0)),
% 1.71/0.60    inference(cnf_transformation,[],[f3])).
% 1.71/0.60  fof(f3,axiom,(
% 1.71/0.60    v1_xboole_0(k1_xboole_0)),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (31027)------------------------------
% 1.71/0.60  % (31027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (31027)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (31027)Memory used [KB]: 2046
% 1.71/0.60  % (31027)Time elapsed: 0.178 s
% 1.71/0.60  % (31027)------------------------------
% 1.71/0.60  % (31027)------------------------------
% 1.87/0.60  % (30997)Success in time 0.238 s
%------------------------------------------------------------------------------
