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
% DateTime   : Thu Dec  3 13:06:09 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  137 (4554 expanded)
%              Number of leaves         :   19 (1373 expanded)
%              Depth                    :   37
%              Number of atoms          :  540 (33085 expanded)
%              Number of equality atoms :  178 (6736 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f578,plain,(
    $false ),
    inference(subsumption_resolution,[],[f577,f547])).

fof(f547,plain,(
    ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f528,f540])).

fof(f540,plain,(
    k1_xboole_0 = sK6 ),
    inference(forward_demodulation,[],[f539,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f539,plain,(
    sK6 = k2_zfmisc_1(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f538,f459])).

fof(f459,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f409,f457])).

fof(f457,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(subsumption_resolution,[],[f240,f454])).

fof(f454,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X1,X2) ),
    inference(subsumption_resolution,[],[f453,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
      | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) )
          & m1_subset_1(sK9(X0,X1,X2,X3),X2)
          & m1_subset_1(sK8(X0,X1,X2,X3),X3) ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ( ( r2_hidden(k4_tarski(X6,X7),X1)
                    | ~ r2_hidden(k4_tarski(X6,X7),X0) )
                  & ( r2_hidden(k4_tarski(X6,X7),X0)
                    | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
                | ~ m1_subset_1(X7,X2) )
            | ~ m1_subset_1(X6,X3) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X1) )
              & ( r2_hidden(k4_tarski(X4,X5),X0)
                | r2_hidden(k4_tarski(X4,X5),X1) )
              & m1_subset_1(X5,X2) )
          & m1_subset_1(X4,X3) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0)
              | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1) )
            & ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0)
              | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1) )
            & m1_subset_1(X5,X2) )
        & m1_subset_1(sK8(X0,X1,X2,X3),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1) )
          & m1_subset_1(X5,X2) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) )
        & ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ? [X5] :
                ( ( ~ r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                & ( r2_hidden(k4_tarski(X4,X5),X0)
                  | r2_hidden(k4_tarski(X4,X5),X1) )
                & m1_subset_1(X5,X2) )
            & m1_subset_1(X4,X3) ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ( ( r2_hidden(k4_tarski(X6,X7),X1)
                    | ~ r2_hidden(k4_tarski(X6,X7),X0) )
                  & ( r2_hidden(k4_tarski(X6,X7),X0)
                    | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
                | ~ m1_subset_1(X7,X2) )
            | ~ m1_subset_1(X6,X3) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP1(X3,X2,X1,X0)
        | ? [X4] :
            ( ? [X5] :
                ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                & ( r2_hidden(k4_tarski(X4,X5),X3)
                  | r2_hidden(k4_tarski(X4,X5),X2) )
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                  & ( r2_hidden(k4_tarski(X4,X5),X3)
                    | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        | ~ sP1(X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP1(X3,X2,X1,X0)
        | ? [X4] :
            ( ? [X5] :
                ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                & ( r2_hidden(k4_tarski(X4,X5),X3)
                  | r2_hidden(k4_tarski(X4,X5),X2) )
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                  & ( r2_hidden(k4_tarski(X4,X5),X3)
                    | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        | ~ sP1(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( sP1(X3,X2,X1,X0)
    <=> ! [X4] :
          ( ! [X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X2)
              <=> r2_hidden(k4_tarski(X4,X5),X3) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f453,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X0,X1,X2),sK9(X0,X0,X1,X2)),X0)
      | sP1(X0,X0,X1,X2) ) ),
    inference(factoring,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0)
      | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f240,plain,
    ( ~ sP1(sK5,sK5,sK4,sK3)
    | r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f235,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X3,X2,X1,X0)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | ~ sP1(X3,X2,X1,X0) )
        & ( sP1(X3,X2,X1,X0)
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> sP1(X3,X2,X1,X0) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f235,plain,(
    sP2(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f227,f53])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ m1_subset_1(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(f227,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | sP2(sK3,sK4,sK5,X7) ) ),
    inference(resolution,[],[f88,f53])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X0,X1,X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f29,f28])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

fof(f409,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f58,f405])).

fof(f405,plain,
    ( sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f404,f221])).

fof(f221,plain,
    ( sK3 = k1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f219,f165])).

fof(f165,plain,(
    k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f72,f53])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f219,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f216,f131])).

fof(f131,plain,(
    sP0(sK3,sK5,sK4) ),
    inference(resolution,[],[f77,f53])).

% (8796)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f216,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 = sK4
    | ~ sP0(sK3,sK5,sK4) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f404,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f402,f223])).

fof(f223,plain,
    ( sK3 = k1_relat_1(sK6)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f220,f166])).

fof(f166,plain,(
    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f72,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f220,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK6)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f217,f132])).

fof(f132,plain,(
    sP0(sK3,sK6,sK4) ),
    inference(resolution,[],[f77,f56])).

fof(f217,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK6)
    | k1_xboole_0 = sK4
    | ~ sP0(sK3,sK6,sK4) ),
    inference(resolution,[],[f73,f55])).

fof(f55,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f402,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f401,f107])).

fof(f107,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f401,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f400,f51])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f400,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f399,f108])).

fof(f108,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f71,f56])).

fof(f399,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f398,f54])).

fof(f54,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f398,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( k1_funct_1(sK5,sK7(sK5,sK6)) != k1_funct_1(sK5,sK7(sK5,sK6))
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f396])).

fof(f396,plain,
    ( k1_funct_1(sK5,sK7(sK5,sK6)) != k1_funct_1(sK5,sK7(sK5,sK6))
    | sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f61,f385])).

fof(f385,plain,
    ( k1_funct_1(sK5,sK7(sK5,sK6)) = k1_funct_1(sK6,sK7(sK5,sK6))
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f384,f57])).

fof(f57,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK3)
      | k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f384,plain,
    ( m1_subset_1(sK7(sK5,sK6),sK3)
    | k1_xboole_0 = sK4
    | sK5 = sK6 ),
    inference(resolution,[],[f382,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f382,plain,
    ( r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f378,f221])).

fof(f378,plain,
    ( r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5))
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f377,f221])).

fof(f377,plain,
    ( sK3 != k1_relat_1(sK5)
    | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5))
    | sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f376,f223])).

fof(f376,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5))
    | sK5 = sK6 ),
    inference(subsumption_resolution,[],[f375,f108])).

fof(f375,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5))
    | ~ v1_relat_1(sK6)
    | sK5 = sK6 ),
    inference(resolution,[],[f339,f54])).

fof(f339,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK5)
      | r2_hidden(sK7(sK5,X0),k1_relat_1(sK5))
      | ~ v1_relat_1(X0)
      | sK5 = X0 ) ),
    inference(subsumption_resolution,[],[f337,f107])).

% (8811)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f337,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK5,X0),k1_relat_1(sK5))
      | k1_relat_1(X0) != k1_relat_1(sK5)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5 = X0
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f538,plain,(
    k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(subsumption_resolution,[],[f537,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f537,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(forward_demodulation,[],[f468,f92])).

fof(f468,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(backward_demodulation,[],[f114,f459])).

fof(f114,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f66,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f528,plain,(
    ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,sK6) ),
    inference(backward_demodulation,[],[f464,f518])).

fof(f518,plain,(
    k1_xboole_0 = sK5 ),
    inference(forward_demodulation,[],[f517,f92])).

fof(f517,plain,(
    sK5 = k2_zfmisc_1(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f516,f459])).

fof(f516,plain,(
    sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f515,f101])).

fof(f515,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(forward_demodulation,[],[f467,f92])).

fof(f467,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f113,f459])).

fof(f113,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(resolution,[],[f65,f102])).

fof(f102,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f66,f53])).

fof(f464,plain,(
    ~ r2_relset_1(sK3,k1_xboole_0,sK5,sK6) ),
    inference(backward_demodulation,[],[f58,f459])).

fof(f577,plain,(
    r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f576,f459])).

fof(f576,plain,(
    r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f575,f518])).

fof(f575,plain,(
    r2_relset_1(sK3,sK4,sK5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f574,f454])).

fof(f574,plain,
    ( ~ sP1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)
    | r2_relset_1(sK3,sK4,sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f481,f518])).

fof(f481,plain,
    ( ~ sP1(k1_xboole_0,sK5,k1_xboole_0,sK3)
    | r2_relset_1(sK3,sK4,sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f239,f459])).

fof(f239,plain,
    ( ~ sP1(k1_xboole_0,sK5,sK4,sK3)
    | r2_relset_1(sK3,sK4,sK5,k1_xboole_0) ),
    inference(resolution,[],[f234,f81])).

fof(f234,plain,(
    sP2(sK3,sK4,sK5,k1_xboole_0) ),
    inference(resolution,[],[f227,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (8815)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (8799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (8818)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (8810)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (8809)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (8808)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (8805)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (8801)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (8800)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (8797)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8802)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (8807)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (8797)Refutation not found, incomplete strategy% (8797)------------------------------
% 0.21/0.53  % (8797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8797)Memory used [KB]: 10618
% 0.21/0.53  % (8797)Time elapsed: 0.109 s
% 0.21/0.53  % (8797)------------------------------
% 0.21/0.53  % (8797)------------------------------
% 0.21/0.53  % (8804)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8814)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.40/0.54  % (8802)Refutation not found, incomplete strategy% (8802)------------------------------
% 1.40/0.54  % (8802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (8802)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (8802)Memory used [KB]: 10618
% 1.40/0.54  % (8802)Time elapsed: 0.080 s
% 1.40/0.54  % (8802)------------------------------
% 1.40/0.54  % (8802)------------------------------
% 1.40/0.54  % (8798)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.40/0.54  % (8817)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.40/0.54  % (8816)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.40/0.54  % (8819)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.40/0.54  % (8806)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.40/0.55  % (8799)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f578,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(subsumption_resolution,[],[f577,f547])).
% 1.40/0.55  fof(f547,plain,(
% 1.40/0.55    ~r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(backward_demodulation,[],[f528,f540])).
% 1.40/0.55  fof(f540,plain,(
% 1.40/0.55    k1_xboole_0 = sK6),
% 1.40/0.55    inference(forward_demodulation,[],[f539,f92])).
% 1.40/0.55  fof(f92,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.40/0.55    inference(equality_resolution,[],[f70])).
% 1.40/0.55  fof(f70,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.40/0.55    inference(flattening,[],[f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.40/0.55    inference(nnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.40/0.55  fof(f539,plain,(
% 1.40/0.55    sK6 = k2_zfmisc_1(sK3,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f538,f459])).
% 1.40/0.55  fof(f459,plain,(
% 1.40/0.55    k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f409,f457])).
% 1.40/0.55  fof(f457,plain,(
% 1.40/0.55    r2_relset_1(sK3,sK4,sK5,sK5)),
% 1.40/0.55    inference(subsumption_resolution,[],[f240,f454])).
% 1.40/0.55  fof(f454,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (sP1(X0,X0,X1,X2)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f453,f87])).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f50])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)) & m1_subset_1(sK9(X0,X1,X2,X3),X2)) & m1_subset_1(sK8(X0,X1,X2,X3),X3))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X1) | ~r2_hidden(k4_tarski(X6,X7),X0)) & (r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X1))) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X3)) | ~sP1(X0,X1,X2,X3)))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f47,f49,f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1)) & m1_subset_1(X5,X2)) & m1_subset_1(X4,X3)) => (? [X5] : ((~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1)) & m1_subset_1(X5,X2)) & m1_subset_1(sK8(X0,X1,X2,X3),X3)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X5),X1)) & m1_subset_1(X5,X2)) => ((~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1)) & m1_subset_1(sK9(X0,X1,X2,X3),X2)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1)) & m1_subset_1(X5,X2)) & m1_subset_1(X4,X3))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X1) | ~r2_hidden(k4_tarski(X6,X7),X0)) & (r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X1))) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X3)) | ~sP1(X0,X1,X2,X3)))),
% 1.40/0.55    inference(rectify,[],[f46])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    ! [X3,X2,X1,X0] : ((sP1(X3,X2,X1,X0) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~sP1(X3,X2,X1,X0)))),
% 1.40/0.55    inference(flattening,[],[f45])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ! [X3,X2,X1,X0] : ((sP1(X3,X2,X1,X0) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~sP1(X3,X2,X1,X0)))),
% 1.40/0.55    inference(nnf_transformation,[],[f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X3,X2,X1,X0] : (sP1(X3,X2,X1,X0) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)))),
% 1.40/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.40/0.55  fof(f453,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X0,X1,X2),sK9(X0,X0,X1,X2)),X0) | sP1(X0,X0,X1,X2)) )),
% 1.40/0.55    inference(factoring,[],[f86])).
% 1.40/0.55  fof(f86,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3)),X1) | sP1(X0,X1,X2,X3)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f50])).
% 1.40/0.55  fof(f240,plain,(
% 1.40/0.55    ~sP1(sK5,sK5,sK4,sK3) | r2_relset_1(sK3,sK4,sK5,sK5)),
% 1.40/0.55    inference(resolution,[],[f235,f81])).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | ~sP1(X3,X2,X1,X0) | r2_relset_1(X0,X1,X2,X3)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | ~sP1(X3,X2,X1,X0)) & (sP1(X3,X2,X1,X0) | ~r2_relset_1(X0,X1,X2,X3))) | ~sP2(X0,X1,X2,X3))),
% 1.40/0.55    inference(nnf_transformation,[],[f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> sP1(X3,X2,X1,X0)) | ~sP2(X0,X1,X2,X3))),
% 1.40/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.40/0.55  fof(f235,plain,(
% 1.40/0.55    sP2(sK3,sK4,sK5,sK5)),
% 1.40/0.55    inference(resolution,[],[f227,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f32,f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f15,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.40/0.55    inference(flattening,[],[f14])).
% 1.40/0.55  fof(f14,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.40/0.55    inference(negated_conjecture,[],[f12])).
% 1.40/0.55  fof(f12,conjecture,(
% 1.40/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 1.40/0.55  fof(f227,plain,(
% 1.40/0.55    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | sP2(sK3,sK4,sK5,X7)) )),
% 1.40/0.55    inference(resolution,[],[f88,f53])).
% 1.40/0.55  fof(f88,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X1,X2,X3)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : (sP2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(definition_folding,[],[f23,f29,f28])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).
% 1.40/0.55  fof(f409,plain,(
% 1.40/0.55    ~r2_relset_1(sK3,sK4,sK5,sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f58,f405])).
% 1.40/0.55  fof(f405,plain,(
% 1.40/0.55    sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f404,f221])).
% 1.40/0.55  fof(f221,plain,(
% 1.40/0.55    sK3 = k1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f219,f165])).
% 1.40/0.55  fof(f165,plain,(
% 1.40/0.55    k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5)),
% 1.40/0.55    inference(resolution,[],[f72,f53])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.55  fof(f219,plain,(
% 1.40/0.55    sK3 = k1_relset_1(sK3,sK4,sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f216,f131])).
% 1.40/0.55  fof(f131,plain,(
% 1.40/0.55    sP0(sK3,sK5,sK4)),
% 1.40/0.55    inference(resolution,[],[f77,f53])).
% 1.40/0.55  % (8796)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.40/0.55  fof(f77,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(definition_folding,[],[f22,f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.40/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.55  fof(f216,plain,(
% 1.40/0.55    sK3 = k1_relset_1(sK3,sK4,sK5) | k1_xboole_0 = sK4 | ~sP0(sK3,sK5,sK4)),
% 1.40/0.55    inference(resolution,[],[f73,f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    v1_funct_2(sK5,sK3,sK4)),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f42])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.40/0.55    inference(rectify,[],[f41])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f26])).
% 1.40/0.55  fof(f404,plain,(
% 1.40/0.55    sK3 != k1_relat_1(sK5) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f403])).
% 1.40/0.55  fof(f403,plain,(
% 1.40/0.55    sK3 != k1_relat_1(sK5) | sK5 = sK6 | k1_xboole_0 = sK4 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f402,f223])).
% 1.40/0.55  fof(f223,plain,(
% 1.40/0.55    sK3 = k1_relat_1(sK6) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f220,f166])).
% 1.40/0.55  fof(f166,plain,(
% 1.40/0.55    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6)),
% 1.40/0.55    inference(resolution,[],[f72,f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f220,plain,(
% 1.40/0.55    sK3 = k1_relset_1(sK3,sK4,sK6) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f217,f132])).
% 1.40/0.55  fof(f132,plain,(
% 1.40/0.55    sP0(sK3,sK6,sK4)),
% 1.40/0.55    inference(resolution,[],[f77,f56])).
% 1.40/0.55  fof(f217,plain,(
% 1.40/0.55    sK3 = k1_relset_1(sK3,sK4,sK6) | k1_xboole_0 = sK4 | ~sP0(sK3,sK6,sK4)),
% 1.40/0.55    inference(resolution,[],[f73,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    v1_funct_2(sK6,sK3,sK4)),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f402,plain,(
% 1.40/0.55    k1_relat_1(sK6) != k1_relat_1(sK5) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f401,f107])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    v1_relat_1(sK5)),
% 1.40/0.55    inference(resolution,[],[f71,f53])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.55  fof(f401,plain,(
% 1.40/0.55    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f400,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    v1_funct_1(sK5)),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f400,plain,(
% 1.40/0.55    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f399,f108])).
% 1.40/0.55  fof(f108,plain,(
% 1.40/0.55    v1_relat_1(sK6)),
% 1.40/0.55    inference(resolution,[],[f71,f56])).
% 1.40/0.55  fof(f399,plain,(
% 1.40/0.55    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f398,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    v1_funct_1(sK6)),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f398,plain,(
% 1.40/0.55    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f397])).
% 1.40/0.55  fof(f397,plain,(
% 1.40/0.55    k1_funct_1(sK5,sK7(sK5,sK6)) != k1_funct_1(sK5,sK7(sK5,sK6)) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | k1_xboole_0 = sK4),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f396])).
% 1.40/0.55  fof(f396,plain,(
% 1.40/0.55    k1_funct_1(sK5,sK7(sK5,sK6)) != k1_funct_1(sK5,sK7(sK5,sK6)) | sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f61,f385])).
% 1.40/0.55  fof(f385,plain,(
% 1.40/0.55    k1_funct_1(sK5,sK7(sK5,sK6)) = k1_funct_1(sK6,sK7(sK5,sK6)) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(resolution,[],[f384,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X4] : (~m1_subset_1(X4,sK3) | k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f384,plain,(
% 1.40/0.55    m1_subset_1(sK7(sK5,sK6),sK3) | k1_xboole_0 = sK4 | sK5 = sK6),
% 1.40/0.55    inference(resolution,[],[f382,f62])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.40/0.55  fof(f382,plain,(
% 1.40/0.55    r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f381])).
% 1.40/0.55  fof(f381,plain,(
% 1.40/0.55    r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | k1_xboole_0 = sK4 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f378,f221])).
% 1.40/0.55  fof(f378,plain,(
% 1.40/0.55    r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5)) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(subsumption_resolution,[],[f377,f221])).
% 1.40/0.55  fof(f377,plain,(
% 1.40/0.55    sK3 != k1_relat_1(sK5) | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5)) | sK5 = sK6 | k1_xboole_0 = sK4),
% 1.40/0.55    inference(superposition,[],[f376,f223])).
% 1.40/0.55  fof(f376,plain,(
% 1.40/0.55    k1_relat_1(sK6) != k1_relat_1(sK5) | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5)) | sK5 = sK6),
% 1.40/0.55    inference(subsumption_resolution,[],[f375,f108])).
% 1.40/0.55  fof(f375,plain,(
% 1.40/0.55    k1_relat_1(sK6) != k1_relat_1(sK5) | r2_hidden(sK7(sK5,sK6),k1_relat_1(sK5)) | ~v1_relat_1(sK6) | sK5 = sK6),
% 1.40/0.55    inference(resolution,[],[f339,f54])).
% 1.40/0.55  fof(f339,plain,(
% 1.40/0.55    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK5) | r2_hidden(sK7(sK5,X0),k1_relat_1(sK5)) | ~v1_relat_1(X0) | sK5 = X0) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f337,f107])).
% 1.40/0.55  % (8811)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.40/0.55  fof(f337,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(sK7(sK5,X0),k1_relat_1(sK5)) | k1_relat_1(X0) != k1_relat_1(sK5) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5 = X0 | ~v1_relat_1(sK5)) )),
% 1.40/0.55    inference(resolution,[],[f60,f51])).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f16])).
% 1.40/0.55  fof(f16,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f35])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f538,plain,(
% 1.40/0.55    k2_zfmisc_1(sK3,sK4) = sK6),
% 1.40/0.55    inference(subsumption_resolution,[],[f537,f101])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.55    inference(resolution,[],[f66,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.40/0.55  fof(f66,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.55  fof(f537,plain,(
% 1.40/0.55    ~r1_tarski(k1_xboole_0,sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 1.40/0.55    inference(forward_demodulation,[],[f468,f92])).
% 1.40/0.55  fof(f468,plain,(
% 1.40/0.55    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 1.40/0.55    inference(backward_demodulation,[],[f114,f459])).
% 1.40/0.55  fof(f114,plain,(
% 1.40/0.55    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 1.40/0.55    inference(resolution,[],[f65,f103])).
% 1.40/0.55  fof(f103,plain,(
% 1.40/0.55    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))),
% 1.40/0.55    inference(resolution,[],[f66,f56])).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f528,plain,(
% 1.40/0.55    ~r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,sK6)),
% 1.40/0.55    inference(backward_demodulation,[],[f464,f518])).
% 1.40/0.55  fof(f518,plain,(
% 1.40/0.55    k1_xboole_0 = sK5),
% 1.40/0.55    inference(forward_demodulation,[],[f517,f92])).
% 1.40/0.55  fof(f517,plain,(
% 1.40/0.55    sK5 = k2_zfmisc_1(sK3,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f516,f459])).
% 1.40/0.55  fof(f516,plain,(
% 1.40/0.55    sK5 = k2_zfmisc_1(sK3,sK4)),
% 1.40/0.55    inference(subsumption_resolution,[],[f515,f101])).
% 1.40/0.55  fof(f515,plain,(
% 1.40/0.55    ~r1_tarski(k1_xboole_0,sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 1.40/0.55    inference(forward_demodulation,[],[f467,f92])).
% 1.40/0.55  fof(f467,plain,(
% 1.40/0.55    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 1.40/0.55    inference(backward_demodulation,[],[f113,f459])).
% 1.40/0.55  fof(f113,plain,(
% 1.40/0.55    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 1.40/0.55    inference(resolution,[],[f65,f102])).
% 1.40/0.55  fof(f102,plain,(
% 1.40/0.55    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))),
% 1.40/0.55    inference(resolution,[],[f66,f53])).
% 1.40/0.55  fof(f464,plain,(
% 1.40/0.55    ~r2_relset_1(sK3,k1_xboole_0,sK5,sK6)),
% 1.40/0.55    inference(backward_demodulation,[],[f58,f459])).
% 1.40/0.55  fof(f577,plain,(
% 1.40/0.55    r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f576,f459])).
% 1.40/0.55  fof(f576,plain,(
% 1.40/0.55    r2_relset_1(sK3,sK4,k1_xboole_0,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f575,f518])).
% 1.40/0.55  fof(f575,plain,(
% 1.40/0.55    r2_relset_1(sK3,sK4,sK5,k1_xboole_0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f574,f454])).
% 1.40/0.55  fof(f574,plain,(
% 1.40/0.55    ~sP1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) | r2_relset_1(sK3,sK4,sK5,k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f481,f518])).
% 1.40/0.55  fof(f481,plain,(
% 1.40/0.55    ~sP1(k1_xboole_0,sK5,k1_xboole_0,sK3) | r2_relset_1(sK3,sK4,sK5,k1_xboole_0)),
% 1.40/0.55    inference(backward_demodulation,[],[f239,f459])).
% 1.40/0.55  fof(f239,plain,(
% 1.40/0.55    ~sP1(k1_xboole_0,sK5,sK4,sK3) | r2_relset_1(sK3,sK4,sK5,k1_xboole_0)),
% 1.40/0.55    inference(resolution,[],[f234,f81])).
% 1.40/0.55  fof(f234,plain,(
% 1.40/0.55    sP2(sK3,sK4,sK5,k1_xboole_0)),
% 1.40/0.55    inference(resolution,[],[f227,f59])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (8799)------------------------------
% 1.40/0.55  % (8799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (8799)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (8799)Memory used [KB]: 6652
% 1.40/0.55  % (8799)Time elapsed: 0.136 s
% 1.40/0.55  % (8799)------------------------------
% 1.40/0.55  % (8799)------------------------------
% 1.40/0.55  % (8793)Success in time 0.188 s
%------------------------------------------------------------------------------
