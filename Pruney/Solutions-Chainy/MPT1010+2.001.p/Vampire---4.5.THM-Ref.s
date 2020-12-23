%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:50 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 162 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  319 ( 578 expanded)
%              Number of equality atoms :  153 ( 237 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f667,plain,(
    $false ),
    inference(subsumption_resolution,[],[f644,f71])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f644,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f121,f505])).

fof(f505,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f503,f69])).

fof(f69,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f503,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f496,f264])).

fof(f264,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f261,f120])).

fof(f120,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f67,f118])).

fof(f118,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f117])).

fof(f117,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f85,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f261,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f232,f119])).

fof(f119,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f68,f118])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f232,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f102,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

% (6190)Refutation not found, incomplete strategy% (6190)------------------------------
% (6190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6190)Termination reason: Refutation not found, incomplete strategy

% (6190)Memory used [KB]: 10874
% (6190)Time elapsed: 0.218 s
% (6190)------------------------------
% (6190)------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f496,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(superposition,[],[f70,f490])).

fof(f490,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f489,f121])).

fof(f489,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK1 = k1_funct_1(sK3,X0)
      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK1 = k1_funct_1(sK3,X0)
      | sK1 = k1_funct_1(sK3,X0)
      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f438,f222])).

fof(f222,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X13,k2_enumset1(X14,X14,X12,X15))
      | X13 = X14
      | X13 = X15
      | v1_xboole_0(k2_enumset1(X14,X14,X12,X15))
      | X12 = X13 ) ),
    inference(resolution,[],[f148,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f148,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f109,f97])).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK9(X0,X1,X2,X3) != X2
              & sK9(X0,X1,X2,X3) != X1
              & sK9(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sK9(X0,X1,X2,X3) = X2
            | sK9(X0,X1,X2,X3) = X1
            | sK9(X0,X1,X2,X3) = X0
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f63,f64])).

fof(f64,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK9(X0,X1,X2,X3) != X2
            & sK9(X0,X1,X2,X3) != X1
            & sK9(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sK9(X0,X1,X2,X3) = X2
          | sK9(X0,X1,X2,X3) = X1
          | sK9(X0,X1,X2,X3) = X0
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f438,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f434,f119])).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X0),X1) ) ),
    inference(resolution,[],[f431,f119])).

fof(f431,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ) ),
    inference(resolution,[],[f294,f66])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f294,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | m1_subset_1(k1_funct_1(X0,X1),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X2))) ) ),
    inference(resolution,[],[f213,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f213,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_relat_1(X1,X2)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | m1_subset_1(k1_funct_1(X1,X0),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f108,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f70,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f72,f118])).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (6168)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (6184)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.47/0.56  % (6185)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.47/0.57  % (6176)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.47/0.57  % (6177)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.58  % (6169)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.77/0.59  % (6165)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.77/0.59  % (6164)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.77/0.60  % (6162)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.77/0.60  % (6167)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.77/0.60  % (6175)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.77/0.60  % (6174)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.77/0.61  % (6191)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.77/0.61  % (6176)Refutation not found, incomplete strategy% (6176)------------------------------
% 1.77/0.61  % (6176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (6176)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.61  
% 1.77/0.61  % (6176)Memory used [KB]: 1918
% 1.77/0.61  % (6176)Time elapsed: 0.189 s
% 1.77/0.61  % (6176)------------------------------
% 1.77/0.61  % (6176)------------------------------
% 1.77/0.62  % (6163)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.77/0.62  % (6163)Refutation not found, incomplete strategy% (6163)------------------------------
% 1.77/0.62  % (6163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (6163)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.62  
% 1.77/0.62  % (6163)Memory used [KB]: 1663
% 1.77/0.62  % (6163)Time elapsed: 0.187 s
% 1.77/0.62  % (6163)------------------------------
% 1.77/0.62  % (6163)------------------------------
% 1.77/0.62  % (6183)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.77/0.62  % (6187)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.77/0.62  % (6166)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.77/0.62  % (6180)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.77/0.63  % (6189)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.77/0.63  % (6186)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.77/0.63  % (6181)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.77/0.63  % (6173)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.77/0.63  % (6178)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.77/0.63  % (6172)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.77/0.63  % (6191)Refutation not found, incomplete strategy% (6191)------------------------------
% 1.77/0.63  % (6191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.63  % (6178)Refutation not found, incomplete strategy% (6178)------------------------------
% 1.77/0.63  % (6178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.64  % (6179)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.77/0.64  % (6188)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.77/0.64  % (6170)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.77/0.64  % (6190)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.77/0.64  % (6182)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.77/0.64  % (6191)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.64  
% 1.77/0.64  % (6191)Memory used [KB]: 1663
% 1.77/0.64  % (6191)Time elapsed: 0.211 s
% 1.77/0.64  % (6191)------------------------------
% 1.77/0.64  % (6191)------------------------------
% 1.77/0.65  % (6171)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.77/0.65  % (6178)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.65  
% 1.77/0.65  % (6178)Memory used [KB]: 10746
% 1.77/0.65  % (6178)Time elapsed: 0.208 s
% 1.77/0.65  % (6178)------------------------------
% 1.77/0.65  % (6178)------------------------------
% 1.77/0.65  % (6184)Refutation found. Thanks to Tanya!
% 1.77/0.65  % SZS status Theorem for theBenchmark
% 1.77/0.65  % SZS output start Proof for theBenchmark
% 1.77/0.65  fof(f667,plain,(
% 1.77/0.65    $false),
% 1.77/0.65    inference(subsumption_resolution,[],[f644,f71])).
% 1.77/0.65  fof(f71,plain,(
% 1.77/0.65    v1_xboole_0(k1_xboole_0)),
% 1.77/0.65    inference(cnf_transformation,[],[f2])).
% 1.77/0.65  fof(f2,axiom,(
% 1.77/0.65    v1_xboole_0(k1_xboole_0)),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.77/0.65  fof(f644,plain,(
% 1.77/0.65    ~v1_xboole_0(k1_xboole_0)),
% 1.77/0.65    inference(superposition,[],[f121,f505])).
% 1.77/0.65  fof(f505,plain,(
% 1.77/0.65    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.77/0.65    inference(subsumption_resolution,[],[f503,f69])).
% 1.77/0.65  fof(f69,plain,(
% 1.77/0.65    r2_hidden(sK2,sK0)),
% 1.77/0.65    inference(cnf_transformation,[],[f44])).
% 1.77/0.65  fof(f44,plain,(
% 1.77/0.65    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.77/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f43])).
% 1.77/0.65  fof(f43,plain,(
% 1.77/0.65    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.77/0.65    introduced(choice_axiom,[])).
% 1.77/0.65  fof(f25,plain,(
% 1.77/0.65    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.77/0.65    inference(flattening,[],[f24])).
% 1.77/0.65  fof(f24,plain,(
% 1.77/0.65    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.77/0.65    inference(ennf_transformation,[],[f23])).
% 1.77/0.65  fof(f23,negated_conjecture,(
% 1.77/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.77/0.65    inference(negated_conjecture,[],[f22])).
% 1.77/0.65  fof(f22,conjecture,(
% 1.77/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.77/0.65  fof(f503,plain,(
% 1.77/0.65    ~r2_hidden(sK2,sK0) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.77/0.65    inference(superposition,[],[f496,f264])).
% 1.77/0.65  fof(f264,plain,(
% 1.77/0.65    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.77/0.65    inference(subsumption_resolution,[],[f261,f120])).
% 1.77/0.65  fof(f120,plain,(
% 1.77/0.65    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.77/0.65    inference(definition_unfolding,[],[f67,f118])).
% 1.77/0.65  fof(f118,plain,(
% 1.77/0.65    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.77/0.65    inference(definition_unfolding,[],[f74,f117])).
% 1.77/0.65  fof(f117,plain,(
% 1.77/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.77/0.65    inference(definition_unfolding,[],[f85,f97])).
% 1.77/0.65  fof(f97,plain,(
% 1.77/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.77/0.65    inference(cnf_transformation,[],[f7])).
% 1.77/0.65  fof(f7,axiom,(
% 1.77/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.77/0.65  fof(f85,plain,(
% 1.77/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.77/0.65    inference(cnf_transformation,[],[f6])).
% 1.77/0.65  fof(f6,axiom,(
% 1.77/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.77/0.65  fof(f74,plain,(
% 1.77/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.77/0.65    inference(cnf_transformation,[],[f5])).
% 1.77/0.65  fof(f5,axiom,(
% 1.77/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.77/0.65  fof(f67,plain,(
% 1.77/0.65    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.77/0.65    inference(cnf_transformation,[],[f44])).
% 1.77/0.65  fof(f261,plain,(
% 1.77/0.65    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relat_1(sK3)),
% 1.77/0.65    inference(resolution,[],[f232,f119])).
% 1.77/0.65  fof(f119,plain,(
% 1.77/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.77/0.65    inference(definition_unfolding,[],[f68,f118])).
% 1.77/0.65  fof(f68,plain,(
% 1.77/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.77/0.65    inference(cnf_transformation,[],[f44])).
% 1.77/0.65  fof(f232,plain,(
% 1.77/0.65    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 1.77/0.65    inference(duplicate_literal_removal,[],[f229])).
% 1.77/0.65  fof(f229,plain,(
% 1.77/0.65    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.77/0.65    inference(superposition,[],[f102,f99])).
% 1.77/0.65  fof(f99,plain,(
% 1.77/0.65    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.65    inference(cnf_transformation,[],[f36])).
% 1.77/0.65  fof(f36,plain,(
% 1.77/0.65    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.65    inference(ennf_transformation,[],[f20])).
% 1.77/0.65  % (6190)Refutation not found, incomplete strategy% (6190)------------------------------
% 1.77/0.65  % (6190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.65  % (6190)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.65  
% 1.77/0.65  % (6190)Memory used [KB]: 10874
% 1.77/0.65  % (6190)Time elapsed: 0.218 s
% 1.77/0.65  % (6190)------------------------------
% 1.77/0.65  % (6190)------------------------------
% 1.77/0.65  fof(f20,axiom,(
% 1.77/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.77/0.65  fof(f102,plain,(
% 1.77/0.65    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.65    inference(cnf_transformation,[],[f60])).
% 1.77/0.65  fof(f60,plain,(
% 1.77/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.65    inference(nnf_transformation,[],[f39])).
% 1.77/0.65  fof(f39,plain,(
% 1.77/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.65    inference(flattening,[],[f38])).
% 1.77/0.65  fof(f38,plain,(
% 1.77/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.65    inference(ennf_transformation,[],[f21])).
% 1.77/0.65  fof(f21,axiom,(
% 1.77/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.77/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.77/0.65  fof(f496,plain,(
% 1.77/0.65    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.77/0.65    inference(trivial_inequality_removal,[],[f491])).
% 1.77/0.65  fof(f491,plain,(
% 1.77/0.65    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.77/0.65    inference(superposition,[],[f70,f490])).
% 1.77/0.65  fof(f490,plain,(
% 1.77/0.65    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.77/0.65    inference(subsumption_resolution,[],[f489,f121])).
% 1.77/0.65  fof(f489,plain,(
% 1.77/0.65    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,X0) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.77/0.65    inference(duplicate_literal_removal,[],[f488])).
% 1.77/0.65  fof(f488,plain,(
% 1.77/0.65    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,X0)) )),
% 1.77/0.65    inference(resolution,[],[f438,f222])).
% 1.77/0.65  fof(f222,plain,(
% 1.77/0.65    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X13,k2_enumset1(X14,X14,X12,X15)) | X13 = X14 | X13 = X15 | v1_xboole_0(k2_enumset1(X14,X14,X12,X15)) | X12 = X13) )),
% 1.77/0.65    inference(resolution,[],[f148,f88])).
% 1.77/0.65  fof(f88,plain,(
% 1.77/0.65    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.77/0.65    inference(cnf_transformation,[],[f33])).
% 1.77/0.65  fof(f33,plain,(
% 1.77/0.65    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.77/0.65    inference(flattening,[],[f32])).
% 2.24/0.65  fof(f32,plain,(
% 2.24/0.65    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.24/0.65    inference(ennf_transformation,[],[f12])).
% 2.24/0.65  fof(f12,axiom,(
% 2.24/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.24/0.65  fof(f148,plain,(
% 2.24/0.65    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.24/0.65    inference(equality_resolution,[],[f129])).
% 2.24/0.65  fof(f129,plain,(
% 2.24/0.65    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.24/0.65    inference(definition_unfolding,[],[f109,f97])).
% 2.24/0.65  fof(f109,plain,(
% 2.24/0.65    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.24/0.65    inference(cnf_transformation,[],[f65])).
% 2.24/0.65  fof(f65,plain,(
% 2.24/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK9(X0,X1,X2,X3) != X2 & sK9(X0,X1,X2,X3) != X1 & sK9(X0,X1,X2,X3) != X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sK9(X0,X1,X2,X3) = X2 | sK9(X0,X1,X2,X3) = X1 | sK9(X0,X1,X2,X3) = X0 | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f63,f64])).
% 2.24/0.65  fof(f64,plain,(
% 2.24/0.65    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK9(X0,X1,X2,X3) != X2 & sK9(X0,X1,X2,X3) != X1 & sK9(X0,X1,X2,X3) != X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sK9(X0,X1,X2,X3) = X2 | sK9(X0,X1,X2,X3) = X1 | sK9(X0,X1,X2,X3) = X0 | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 2.24/0.65    introduced(choice_axiom,[])).
% 2.24/0.65  fof(f63,plain,(
% 2.24/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.65    inference(rectify,[],[f62])).
% 2.24/0.65  fof(f62,plain,(
% 2.24/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.65    inference(flattening,[],[f61])).
% 2.24/0.65  fof(f61,plain,(
% 2.24/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.65    inference(nnf_transformation,[],[f42])).
% 2.24/0.65  fof(f42,plain,(
% 2.24/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.24/0.65    inference(ennf_transformation,[],[f4])).
% 2.24/0.65  fof(f4,axiom,(
% 2.24/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.24/0.65  fof(f438,plain,(
% 2.24/0.65    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 2.24/0.65    inference(resolution,[],[f434,f119])).
% 2.24/0.65  fof(f434,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1)) )),
% 2.24/0.65    inference(resolution,[],[f431,f119])).
% 2.24/0.65  fof(f431,plain,(
% 2.24/0.65    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))) )),
% 2.24/0.65    inference(resolution,[],[f294,f66])).
% 2.24/0.65  fof(f66,plain,(
% 2.24/0.65    v1_funct_1(sK3)),
% 2.24/0.65    inference(cnf_transformation,[],[f44])).
% 2.24/0.65  fof(f294,plain,(
% 2.24/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | m1_subset_1(k1_funct_1(X0,X1),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X2)))) )),
% 2.24/0.65    inference(resolution,[],[f213,f101])).
% 2.24/0.65  fof(f101,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/0.65    inference(cnf_transformation,[],[f37])).
% 2.24/0.65  fof(f37,plain,(
% 2.24/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.65    inference(ennf_transformation,[],[f18])).
% 2.24/0.65  fof(f18,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.24/0.65  fof(f213,plain,(
% 2.24/0.65    ( ! [X4,X2,X0,X3,X1] : (~v5_relat_1(X1,X2) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | m1_subset_1(k1_funct_1(X1,X0),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.24/0.65    inference(resolution,[],[f108,f98])).
% 2.24/0.65  fof(f98,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/0.65    inference(cnf_transformation,[],[f35])).
% 2.24/0.65  fof(f35,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/0.65    inference(ennf_transformation,[],[f17])).
% 2.24/0.65  fof(f17,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.24/0.65  fof(f108,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f41])).
% 2.24/0.65  fof(f41,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.24/0.65    inference(flattening,[],[f40])).
% 2.24/0.65  fof(f40,plain,(
% 2.24/0.65    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.24/0.65    inference(ennf_transformation,[],[f14])).
% 2.24/0.65  fof(f14,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 2.24/0.65  fof(f70,plain,(
% 2.24/0.65    sK1 != k1_funct_1(sK3,sK2)),
% 2.24/0.65    inference(cnf_transformation,[],[f44])).
% 2.24/0.65  fof(f121,plain,(
% 2.24/0.65    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.24/0.65    inference(definition_unfolding,[],[f72,f118])).
% 2.24/0.65  fof(f72,plain,(
% 2.24/0.65    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.24/0.65    inference(cnf_transformation,[],[f9])).
% 2.24/0.65  fof(f9,axiom,(
% 2.24/0.65    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.24/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.24/0.65  % SZS output end Proof for theBenchmark
% 2.24/0.65  % (6184)------------------------------
% 2.24/0.65  % (6184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.65  % (6184)Termination reason: Refutation
% 2.24/0.65  
% 2.24/0.65  % (6184)Memory used [KB]: 6908
% 2.24/0.65  % (6184)Time elapsed: 0.214 s
% 2.24/0.65  % (6184)------------------------------
% 2.24/0.65  % (6184)------------------------------
% 2.24/0.66  % (6161)Success in time 0.292 s
%------------------------------------------------------------------------------
