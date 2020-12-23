%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  177 (402405 expanded)
%              Number of leaves         :   15 (115280 expanded)
%              Depth                    :   86
%              Number of atoms          :  742 (3627163 expanded)
%              Number of equality atoms :  253 (1140689 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(subsumption_resolution,[],[f463,f448])).

fof(f448,plain,(
    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f50,f446])).

fof(f446,plain,(
    r1_partfun1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f445,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f445,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_partfun1(sK3,sK4) ),
    inference(forward_demodulation,[],[f444,f346])).

fof(f346,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f284,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f284,plain,(
    r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f265])).

fof(f265,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f47,f264])).

fof(f264,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f263,f236])).

fof(f236,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f234,f50])).

fof(f234,plain,
    ( r1_partfun1(sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f232,f101])).

fof(f232,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | r1_partfun1(sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | r1_partfun1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f229,f108])).

fof(f108,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f107,f87])).

fof(f87,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f59,f46])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
        & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) )
      | ~ r1_partfun1(sK3,sK4) )
    & ( ! [X5] :
          ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
      | r1_partfun1(sK3,sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(sK3,X4)
                & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
            | ~ r1_partfun1(sK3,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X3,X5) = k1_funct_1(sK3,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
            | r1_partfun1(sK3,X3) )
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK3,X4)
              & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
          | ~ r1_partfun1(sK3,X3) )
        & ( ! [X5] :
              ( k1_funct_1(X3,X5) = k1_funct_1(sK3,X5)
              | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
          | r1_partfun1(sK3,X3) )
        & ( k1_xboole_0 = sK1
          | k1_xboole_0 != sK2 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ( ? [X4] :
            ( k1_funct_1(sK3,X4) != k1_funct_1(sK4,X4)
            & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
        | ~ r1_partfun1(sK3,sK4) )
      & ( ! [X5] :
            ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
            | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
        | r1_partfun1(sK3,sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( k1_funct_1(sK3,X4) != k1_funct_1(sK4,X4)
        & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
   => ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
      & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f107,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f106,f80])).

fof(f80,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f65,f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f106,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f229,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | r1_partfun1(sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f228,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f228,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f227,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f227,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f226,f77])).

fof(f77,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f58,f46])).

fof(f226,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f225,f44])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f225,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) != k1_funct_1(sK3,sK6(sK3,sK4))
    | r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f54,f223])).

fof(f223,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f222,f167])).

fof(f167,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(resolution,[],[f165,f50])).

fof(f165,plain,
    ( r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f163,f101])).

fof(f163,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f152,f108])).

fof(f152,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f149,f77])).

fof(f149,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | r1_partfun1(sK3,sK4) ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK3,X0)
      | k1_funct_1(sK3,sK6(sK3,X0)) = k1_funct_1(sK4,sK6(sK3,X0))
      | r1_partfun1(sK3,sK4) ) ),
    inference(resolution,[],[f123,f88])).

fof(f88,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK3))
      | k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | r1_partfun1(sK3,sK4) ) ),
    inference(backward_demodulation,[],[f48,f86])).

fof(f86,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f59,f43])).

fof(f48,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f121,f76])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
                & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f222,plain,
    ( k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(resolution,[],[f216,f166])).

fof(f166,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(resolution,[],[f165,f89])).

fof(f89,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f49,f86])).

fof(f49,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_xboole_0 = sK2
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f215,f101])).

fof(f215,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f172,f108])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f171,f76])).

fof(f171,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f170,f42])).

fof(f170,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f77])).

fof(f169,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f168,f44])).

fof(f168,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f165,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f263,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f255,f235])).

fof(f235,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f234,f89])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f254,f101])).

fof(f254,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f241,f108])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f240,f76])).

fof(f240,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f239,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f238,f77])).

fof(f238,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f237,f44])).

fof(f237,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f234,f52])).

fof(f47,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_relat_1(sK3),X0),sK1)
      | r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f95,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r2_hidden(sK7(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f55,f56])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f95,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f93,f86])).

fof(f93,plain,(
    m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f444,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | r1_partfun1(sK3,sK4) ),
    inference(forward_demodulation,[],[f443,f312])).

fof(f312,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f304,f311])).

fof(f311,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f310,f295])).

fof(f295,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f267,f265])).

fof(f267,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f264])).

fof(f310,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(resolution,[],[f298,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f298,plain,(
    sP0(k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f270,f265])).

fof(f270,plain,(
    sP0(sK1,sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f80,f264])).

fof(f304,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(forward_demodulation,[],[f276,f265])).

fof(f276,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f87,f264])).

fof(f443,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f442,f76])).

fof(f442,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f441,f42])).

fof(f441,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f440,f77])).

fof(f440,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f439,f44])).

fof(f439,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) != k1_funct_1(sK3,sK6(sK3,sK4))
    | r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f54,f437])).

fof(f437,plain,(
    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f436,f333])).

fof(f333,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(global_subsumption,[],[f50,f330])).

fof(f330,plain,
    ( r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f316,f284])).

fof(f316,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(backward_demodulation,[],[f152,f312])).

fof(f436,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(resolution,[],[f403,f363])).

fof(f363,plain,
    ( r2_hidden(sK5,k1_xboole_0)
    | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) ),
    inference(backward_demodulation,[],[f332,f346])).

fof(f332,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
    | r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(global_subsumption,[],[f89,f330])).

fof(f403,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f402,f74])).

fof(f402,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(forward_demodulation,[],[f401,f346])).

fof(f401,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(forward_demodulation,[],[f400,f312])).

fof(f400,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) ) ),
    inference(forward_demodulation,[],[f399,f346])).

fof(f399,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f398,f76])).

fof(f398,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f397,f42])).

fof(f397,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f396,f77])).

fof(f396,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f395,f44])).

fof(f395,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f330,f52])).

fof(f50,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f463,plain,(
    k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f458,f447])).

fof(f447,plain,(
    r2_hidden(sK5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f348,f446])).

fof(f348,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | r2_hidden(sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f89,f346])).

fof(f458,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f457,f74])).

fof(f457,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(forward_demodulation,[],[f456,f346])).

fof(f456,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(forward_demodulation,[],[f455,f312])).

fof(f455,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) ) ),
    inference(forward_demodulation,[],[f454,f346])).

fof(f454,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f453,f76])).

fof(f453,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f452,f42])).

fof(f452,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f451,f77])).

fof(f451,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f450,f44])).

fof(f450,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f446,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26322)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (26314)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (26311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (26329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (26312)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (26323)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (26326)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (26309)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (26321)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (26307)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (26308)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (26319)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (26324)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (26313)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26310)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (26334)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (26331)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (26327)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (26336)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (26315)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (26330)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (26317)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (26316)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (26333)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (26317)Refutation not found, incomplete strategy% (26317)------------------------------
% 0.20/0.53  % (26317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26317)Memory used [KB]: 10746
% 0.20/0.53  % (26317)Time elapsed: 0.131 s
% 0.20/0.53  % (26317)------------------------------
% 0.20/0.53  % (26317)------------------------------
% 0.20/0.53  % (26328)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (26332)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (26325)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (26314)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (26335)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (26318)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (26320)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (26333)Refutation not found, incomplete strategy% (26333)------------------------------
% 0.20/0.55  % (26333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26333)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26333)Memory used [KB]: 10874
% 0.20/0.55  % (26333)Time elapsed: 0.146 s
% 0.20/0.55  % (26333)------------------------------
% 0.20/0.55  % (26333)------------------------------
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f464,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(subsumption_resolution,[],[f463,f448])).
% 0.20/0.56  fof(f448,plain,(
% 0.20/0.56    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f50,f446])).
% 0.20/0.56  fof(f446,plain,(
% 0.20/0.56    r1_partfun1(sK3,sK4)),
% 0.20/0.56    inference(subsumption_resolution,[],[f445,f74])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(resolution,[],[f57,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38])).
% 0.20/0.56  fof(f445,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_partfun1(sK3,sK4)),
% 0.20/0.56    inference(forward_demodulation,[],[f444,f346])).
% 0.20/0.56  fof(f346,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.56    inference(resolution,[],[f284,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f101,f265])).
% 0.20/0.56  fof(f265,plain,(
% 0.20/0.56    k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f47,f264])).
% 0.20/0.56  fof(f264,plain,(
% 0.20/0.56    k1_xboole_0 = sK2),
% 0.20/0.56    inference(subsumption_resolution,[],[f263,f236])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | k1_xboole_0 = sK2),
% 0.20/0.56    inference(resolution,[],[f234,f50])).
% 0.20/0.56  fof(f234,plain,(
% 0.20/0.56    r1_partfun1(sK3,sK4) | k1_xboole_0 = sK2),
% 0.20/0.56    inference(subsumption_resolution,[],[f232,f101])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | r1_partfun1(sK3,sK4) | k1_xboole_0 = sK2),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f231])).
% 0.20/0.56  fof(f231,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | r1_partfun1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.56    inference(superposition,[],[f229,f108])).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.20/0.56    inference(superposition,[],[f107,f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.20/0.56    inference(resolution,[],[f59,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(sK4,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(sK4,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) => (k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(rectify,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(nnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.20/0.57    inference(negated_conjecture,[],[f9])).
% 0.20/0.57  fof(f9,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f106,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    sP0(sK1,sK4,sK2)),
% 0.20/0.57    inference(resolution,[],[f65,f46])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(definition_folding,[],[f23,f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 0.20/0.57    inference(resolution,[],[f61,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    v1_funct_2(sK4,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.20/0.57    inference(rectify,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f24])).
% 0.20/0.57  fof(f229,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | r1_partfun1(sK3,sK4) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f228,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f58,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f228,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f227,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f227,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f226,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f58,f46])).
% 0.20/0.57  fof(f226,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f225,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    v1_funct_1(sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f225,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f224])).
% 0.20/0.57  fof(f224,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) != k1_funct_1(sK3,sK6(sK3,sK4)) | r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f54,f223])).
% 0.20/0.57  fof(f223,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f222,f167])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f165,f50])).
% 0.20/0.57  fof(f165,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f163,f101])).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),sK1) | r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f152,f108])).
% 0.20/0.57  fof(f152,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(subsumption_resolution,[],[f149,f77])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f148])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | r1_partfun1(sK3,sK4)),
% 0.20/0.57    inference(resolution,[],[f125,f44])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_partfun1(sK3,X0) | k1_funct_1(sK3,sK6(sK3,X0)) = k1_funct_1(sK4,sK6(sK3,X0)) | r1_partfun1(sK3,sK4)) )),
% 0.20/0.57    inference(resolution,[],[f123,f88])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK3)) | k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | r1_partfun1(sK3,sK4)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f48,f86])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f59,f43])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK3,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f121,f76])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f53,f42])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_partfun1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(rectify,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.20/0.57  fof(f222,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f218])).
% 0.20/0.57  fof(f218,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f216,f166])).
% 0.20/0.57  fof(f166,plain,(
% 0.20/0.57    r2_hidden(sK5,k1_relat_1(sK3)) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f165,f89])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ~r1_partfun1(sK3,sK4) | r2_hidden(sK5,k1_relat_1(sK3))),
% 0.20/0.57    inference(backward_demodulation,[],[f49,f86])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ~r1_partfun1(sK3,sK4) | r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f216,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = sK2 | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f215,f101])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),sK1) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f214])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),sK1) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2) )),
% 0.20/0.57    inference(superposition,[],[f172,f108])).
% 0.20/0.57  fof(f172,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f171,f76])).
% 0.20/0.57  fof(f171,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f170,f42])).
% 0.20/0.57  fof(f170,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f169,f77])).
% 0.20/0.57  fof(f169,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f168,f44])).
% 0.20/0.57  fof(f168,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f165,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (~r1_partfun1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f263,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f257])).
% 0.20/0.57  fof(f257,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(resolution,[],[f255,f235])).
% 0.20/0.57  fof(f235,plain,(
% 0.20/0.57    r2_hidden(sK5,k1_relat_1(sK3)) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(resolution,[],[f234,f89])).
% 0.20/0.57  fof(f255,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_xboole_0 = sK2) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f254,f101])).
% 0.20/0.57  fof(f254,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),sK1) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_xboole_0 = sK2) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f253])).
% 0.20/0.57  fof(f253,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),sK1) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2) )),
% 0.20/0.57    inference(superposition,[],[f241,f108])).
% 0.20/0.57  fof(f241,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | k1_xboole_0 = sK2) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f240,f76])).
% 0.20/0.57  fof(f240,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f239,f42])).
% 0.20/0.57  fof(f239,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f238,f77])).
% 0.20/0.57  fof(f238,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f237,f44])).
% 0.20/0.57  fof(f237,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f234,f52])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    r1_tarski(k1_relat_1(sK3),sK1) | r1_tarski(k1_relat_1(sK3),sK1)),
% 0.20/0.57    inference(resolution,[],[f97,f57])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK7(k1_relat_1(sK3),X0),sK1) | r1_tarski(k1_relat_1(sK3),X0)) )),
% 0.20/0.57    inference(resolution,[],[f95,f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK7(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(resolution,[],[f55,f56])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.20/0.57    inference(forward_demodulation,[],[f93,f86])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 0.20/0.57    inference(resolution,[],[f60,f43])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.57  fof(f444,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | r1_partfun1(sK3,sK4)),
% 0.20/0.57    inference(forward_demodulation,[],[f443,f312])).
% 0.20/0.57  fof(f312,plain,(
% 0.20/0.57    k1_xboole_0 = k1_relat_1(sK4)),
% 0.20/0.57    inference(backward_demodulation,[],[f304,f311])).
% 0.20/0.57  fof(f311,plain,(
% 0.20/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f310,f295])).
% 0.20/0.57  fof(f295,plain,(
% 0.20/0.57    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.20/0.57    inference(forward_demodulation,[],[f267,f265])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 0.20/0.57    inference(backward_demodulation,[],[f45,f264])).
% 0.20/0.57  fof(f310,plain,(
% 0.20/0.57    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.20/0.57    inference(resolution,[],[f298,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f62])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f40])).
% 0.20/0.57  fof(f298,plain,(
% 0.20/0.57    sP0(k1_xboole_0,sK4,k1_xboole_0)),
% 0.20/0.57    inference(forward_demodulation,[],[f270,f265])).
% 0.20/0.57  fof(f270,plain,(
% 0.20/0.57    sP0(sK1,sK4,k1_xboole_0)),
% 0.20/0.57    inference(backward_demodulation,[],[f80,f264])).
% 0.20/0.57  fof(f304,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.20/0.57    inference(forward_demodulation,[],[f276,f265])).
% 0.20/0.57  fof(f276,plain,(
% 0.20/0.57    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4)),
% 0.20/0.57    inference(backward_demodulation,[],[f87,f264])).
% 0.20/0.57  fof(f443,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))),
% 0.20/0.57    inference(subsumption_resolution,[],[f442,f76])).
% 0.20/0.57  fof(f442,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f441,f42])).
% 0.20/0.57  fof(f441,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f440,f77])).
% 0.20/0.57  fof(f440,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f439,f44])).
% 0.20/0.57  fof(f439,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f438])).
% 0.20/0.57  fof(f438,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) != k1_funct_1(sK3,sK6(sK3,sK4)) | r1_partfun1(sK3,sK4) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(superposition,[],[f54,f437])).
% 0.20/0.57  fof(f437,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(subsumption_resolution,[],[f436,f333])).
% 0.20/0.57  fof(f333,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(global_subsumption,[],[f50,f330])).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(subsumption_resolution,[],[f316,f284])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(backward_demodulation,[],[f152,f312])).
% 0.20/0.57  fof(f436,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f433])).
% 0.20/0.57  fof(f433,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(resolution,[],[f403,f363])).
% 0.20/0.57  fof(f363,plain,(
% 0.20/0.57    r2_hidden(sK5,k1_xboole_0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4))),
% 0.20/0.57    inference(backward_demodulation,[],[f332,f346])).
% 0.20/0.57  fof(f332,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | r2_hidden(sK5,k1_relat_1(sK3))),
% 0.20/0.57    inference(global_subsumption,[],[f89,f330])).
% 0.20/0.57  fof(f403,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f402,f74])).
% 0.20/0.57  fof(f402,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f401,f346])).
% 0.20/0.57  fof(f401,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f400,f312])).
% 0.20/0.57  fof(f400,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f399,f346])).
% 0.20/0.57  fof(f399,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f398,f76])).
% 0.20/0.57  fof(f398,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f397,f42])).
% 0.20/0.57  fof(f397,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f396,f77])).
% 0.20/0.57  fof(f396,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f395,f44])).
% 0.20/0.57  fof(f395,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,sK4)) = k1_funct_1(sK4,sK6(sK3,sK4)) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f330,f52])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ~r1_partfun1(sK3,sK4) | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f463,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)),
% 0.20/0.57    inference(resolution,[],[f458,f447])).
% 0.20/0.57  fof(f447,plain,(
% 0.20/0.57    r2_hidden(sK5,k1_xboole_0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f348,f446])).
% 0.20/0.57  fof(f348,plain,(
% 0.20/0.57    ~r1_partfun1(sK3,sK4) | r2_hidden(sK5,k1_xboole_0)),
% 0.20/0.57    inference(backward_demodulation,[],[f89,f346])).
% 0.20/0.57  fof(f458,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f457,f74])).
% 0.20/0.57  fof(f457,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f456,f346])).
% 0.20/0.57  fof(f456,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f455,f312])).
% 0.20/0.57  fof(f455,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f454,f346])).
% 0.20/0.57  fof(f454,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f453,f76])).
% 0.20/0.57  fof(f453,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f452,f42])).
% 0.20/0.57  fof(f452,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f451,f77])).
% 0.20/0.57  fof(f451,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f450,f44])).
% 0.20/0.57  fof(f450,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f446,f52])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (26314)------------------------------
% 0.20/0.57  % (26314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (26314)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (26314)Memory used [KB]: 6524
% 0.20/0.57  % (26314)Time elapsed: 0.145 s
% 0.20/0.57  % (26314)------------------------------
% 0.20/0.57  % (26314)------------------------------
% 0.20/0.57  % (26306)Success in time 0.217 s
%------------------------------------------------------------------------------
