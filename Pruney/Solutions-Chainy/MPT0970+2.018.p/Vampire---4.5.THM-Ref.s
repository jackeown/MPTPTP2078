%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 459 expanded)
%              Number of leaves         :   14 ( 131 expanded)
%              Depth                    :   22
%              Number of atoms          :  320 (2139 expanded)
%              Number of equality atoms :   70 ( 461 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(subsumption_resolution,[],[f381,f326])).

fof(f326,plain,(
    ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f325,f193])).

fof(f193,plain,
    ( k1_xboole_0 != sK1
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f185,f58])).

fof(f58,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f185,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[],[f75,f165])).

fof(f165,plain,(
    ! [X14] :
      ( k1_xboole_0 = k2_relat_1(X14)
      | ~ v1_relat_1(X14)
      | ~ v5_relat_1(X14,k1_xboole_0) ) ),
    inference(resolution,[],[f129,f113])).

fof(f113,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK4(X2,k1_xboole_0))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK4(X3,X4))
      | r2_hidden(sK4(X3,X4),X3)
      | X3 = X4 ) ),
    inference(resolution,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f129,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_relat_1(X2),X3)
      | ~ v5_relat_1(X2,k1_xboole_0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f119,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,sK5(X6,X8))
      | r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f74,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f325,plain,
    ( k1_xboole_0 = sK1
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f324,f218])).

fof(f218,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f217,f89])).

fof(f217,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(sK4(X0,k1_xboole_0),X0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK4(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X1)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f89,f46])).

fof(f324,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f322,f58])).

fof(f322,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[],[f319,f165])).

fof(f319,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f317,f37])).

fof(f317,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f305,f51])).

fof(f305,plain,
    ( r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f138,f47])).

fof(f138,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK5(X3,k2_relset_1(sK0,sK1,sK2)),sK1)
      | k1_xboole_0 = sK1
      | r1_tarski(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f106,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f38,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK3(X0),sK0)
      | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK3(X0),sK0)
      | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f81,f37])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relset_1(X1,X2,sK2))
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(sK2,X1,X2)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f381,plain,(
    v5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f66,f362])).

fof(f362,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f361,f58])).

fof(f361,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f359,f66])).

fof(f359,plain,
    ( k1_xboole_0 = sK1
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f323,f42])).

fof(f323,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f320,f75])).

fof(f320,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f319,f257])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f256,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(factoring,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f44,f46])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r2_hidden(sK4(X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r2_hidden(sK4(X1,X0),X1) ) ),
    inference(resolution,[],[f123,f45])).

fof(f123,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(X1,X2),X3)
      | ~ r1_tarski(X2,X1)
      | X1 = X2
      | ~ r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f94,f46])).

fof(f66,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (28772)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.50  % (28756)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (28746)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (28765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (28757)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (28772)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f406,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(subsumption_resolution,[],[f381,f326])).
% 1.31/0.54  fof(f326,plain,(
% 1.31/0.54    ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f325,f193])).
% 1.31/0.54  fof(f193,plain,(
% 1.31/0.54    k1_xboole_0 != sK1 | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f185,f58])).
% 1.31/0.54  fof(f58,plain,(
% 1.31/0.54    v1_relat_1(sK2)),
% 1.31/0.54    inference(resolution,[],[f50,f37])).
% 1.31/0.54  fof(f37,plain,(
% 1.31/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25,f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f14,plain,(
% 1.31/0.54    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.31/0.54    inference(flattening,[],[f13])).
% 1.31/0.54  fof(f13,plain,(
% 1.31/0.54    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.31/0.54    inference(ennf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,negated_conjecture,(
% 1.31/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.31/0.54    inference(negated_conjecture,[],[f10])).
% 1.31/0.54  fof(f10,conjecture,(
% 1.31/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.31/0.54  fof(f50,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f19])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.54    inference(ennf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.54  fof(f185,plain,(
% 1.31/0.54    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(superposition,[],[f75,f165])).
% 1.31/0.54  fof(f165,plain,(
% 1.31/0.54    ( ! [X14] : (k1_xboole_0 = k2_relat_1(X14) | ~v1_relat_1(X14) | ~v5_relat_1(X14,k1_xboole_0)) )),
% 1.31/0.54    inference(resolution,[],[f129,f113])).
% 1.31/0.54  fof(f113,plain,(
% 1.31/0.54    ( ! [X2] : (~r1_tarski(X2,sK4(X2,k1_xboole_0)) | k1_xboole_0 = X2) )),
% 1.31/0.54    inference(resolution,[],[f89,f49])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f18])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f5])).
% 1.31/0.54  fof(f5,axiom,(
% 1.31/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.31/0.54  fof(f89,plain,(
% 1.31/0.54    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(resolution,[],[f68,f41])).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.31/0.54  fof(f68,plain,(
% 1.31/0.54    ( ! [X4,X3] : (~r1_tarski(X4,sK4(X3,X4)) | r2_hidden(sK4(X3,X4),X3) | X3 = X4) )),
% 1.31/0.54    inference(resolution,[],[f44,f49])).
% 1.31/0.54  fof(f44,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.31/0.54    inference(nnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.31/0.54    inference(ennf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.31/0.54  fof(f129,plain,(
% 1.31/0.54    ( ! [X2,X3] : (r1_tarski(k2_relat_1(X2),X3) | ~v5_relat_1(X2,k1_xboole_0) | ~v1_relat_1(X2)) )),
% 1.31/0.54    inference(resolution,[],[f119,f42])).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,plain,(
% 1.31/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.31/0.54  fof(f119,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(resolution,[],[f84,f41])).
% 1.31/0.54  fof(f84,plain,(
% 1.31/0.54    ( ! [X6,X8,X7] : (~r1_tarski(X7,sK5(X6,X8)) | r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 1.31/0.54    inference(resolution,[],[f63,f49])).
% 1.31/0.54  fof(f63,plain,(
% 1.31/0.54    ( ! [X4,X2,X3] : (r2_hidden(sK5(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 1.31/0.54    inference(resolution,[],[f46,f47])).
% 1.31/0.54  fof(f47,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f34])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.31/0.54  fof(f33,plain,(
% 1.31/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.54    inference(rectify,[],[f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.54    inference(nnf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f1])).
% 1.31/0.54  fof(f1,axiom,(
% 1.31/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.54  fof(f46,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f34])).
% 1.31/0.54  fof(f75,plain,(
% 1.31/0.54    sK1 != k2_relat_1(sK2)),
% 1.31/0.54    inference(subsumption_resolution,[],[f74,f37])).
% 1.31/0.54  fof(f74,plain,(
% 1.31/0.54    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.54    inference(superposition,[],[f40,f51])).
% 1.31/0.54  fof(f51,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f20])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.54    inference(ennf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f325,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f324,f218])).
% 1.31/0.54  fof(f218,plain,(
% 1.31/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f217,f89])).
% 1.31/0.54  fof(f217,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(sK4(X0,k1_xboole_0),X0)) )),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f213])).
% 1.31/0.54  fof(f213,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~r2_hidden(sK4(X0,k1_xboole_0),X0)) )),
% 1.31/0.54    inference(resolution,[],[f112,f45])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK4(X0,X1),X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f112,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,k1_xboole_0),X1) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(resolution,[],[f89,f46])).
% 1.31/0.54  fof(f324,plain,(
% 1.31/0.54    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f322,f58])).
% 1.31/0.54  fof(f322,plain,(
% 1.31/0.54    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(superposition,[],[f319,f165])).
% 1.31/0.54  fof(f319,plain,(
% 1.31/0.54    r1_tarski(sK1,k2_relat_1(sK2)) | k1_xboole_0 = sK1),
% 1.31/0.54    inference(subsumption_resolution,[],[f317,f37])).
% 1.31/0.54  fof(f317,plain,(
% 1.31/0.54    r1_tarski(sK1,k2_relat_1(sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.54    inference(superposition,[],[f305,f51])).
% 1.31/0.54  fof(f305,plain,(
% 1.31/0.54    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f299])).
% 1.31/0.54  fof(f299,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 1.31/0.54    inference(resolution,[],[f138,f47])).
% 1.31/0.54  fof(f138,plain,(
% 1.31/0.54    ( ! [X3] : (~r2_hidden(sK5(X3,k2_relset_1(sK0,sK1,sK2)),sK1) | k1_xboole_0 = sK1 | r1_tarski(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 1.31/0.54    inference(resolution,[],[f106,f48])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f34])).
% 1.31/0.54  fof(f106,plain,(
% 1.31/0.54    ( ! [X0] : (r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK1)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f105,f38])).
% 1.31/0.54  fof(f38,plain,(
% 1.31/0.54    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~r2_hidden(X0,sK1)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f104,f36])).
% 1.31/0.54  fof(f36,plain,(
% 1.31/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f104,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~r2_hidden(X0,sK1)) )),
% 1.31/0.54    inference(resolution,[],[f81,f37])).
% 1.31/0.54  fof(f81,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | ~v1_funct_2(sK2,X1,X2) | ~r2_hidden(X0,sK1)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f78,f35])).
% 1.31/0.54  fof(f35,plain,(
% 1.31/0.54    v1_funct_1(sK2)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f78,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relset_1(X1,X2,sK2)) | k1_xboole_0 = X2 | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 1.31/0.54    inference(superposition,[],[f53,f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f23])).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.31/0.54    inference(flattening,[],[f22])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.31/0.54    inference(ennf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 1.31/0.54  fof(f381,plain,(
% 1.31/0.54    v5_relat_1(sK2,k1_xboole_0)),
% 1.31/0.54    inference(backward_demodulation,[],[f66,f362])).
% 1.31/0.54  fof(f362,plain,(
% 1.31/0.54    k1_xboole_0 = sK1),
% 1.31/0.54    inference(subsumption_resolution,[],[f361,f58])).
% 1.31/0.54  fof(f361,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | ~v1_relat_1(sK2)),
% 1.31/0.54    inference(subsumption_resolution,[],[f359,f66])).
% 1.31/0.54  fof(f359,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.31/0.54    inference(resolution,[],[f323,f42])).
% 1.31/0.54  fof(f323,plain,(
% 1.31/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 1.31/0.54    inference(subsumption_resolution,[],[f320,f75])).
% 1.31/0.54  fof(f320,plain,(
% 1.31/0.54    k1_xboole_0 = sK1 | sK1 = k2_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.31/0.54    inference(resolution,[],[f319,f257])).
% 1.31/0.54  fof(f257,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f256,f94])).
% 1.31/0.54  fof(f94,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 1.31/0.54    inference(factoring,[],[f67])).
% 1.31/0.54  fof(f67,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | r2_hidden(sK4(X0,X1),X0) | X0 = X1 | ~r1_tarski(X1,X2)) )),
% 1.31/0.54    inference(resolution,[],[f44,f46])).
% 1.31/0.54  fof(f256,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~r1_tarski(X1,X0) | ~r2_hidden(sK4(X1,X0),X1)) )),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f252])).
% 1.31/0.54  fof(f252,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~r1_tarski(X1,X0) | X0 = X1 | ~r2_hidden(sK4(X1,X0),X1)) )),
% 1.31/0.54    inference(resolution,[],[f123,f45])).
% 1.31/0.54  fof(f123,plain,(
% 1.31/0.54    ( ! [X2,X3,X1] : (r2_hidden(sK4(X1,X2),X3) | ~r1_tarski(X2,X1) | X1 = X2 | ~r1_tarski(X1,X3)) )),
% 1.31/0.54    inference(resolution,[],[f94,f46])).
% 1.31/0.54  fof(f66,plain,(
% 1.31/0.54    v5_relat_1(sK2,sK1)),
% 1.31/0.54    inference(resolution,[],[f52,f37])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f21])).
% 1.31/0.54  fof(f21,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.54    inference(ennf_transformation,[],[f12])).
% 1.31/0.54  fof(f12,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.31/0.54    inference(pure_predicate_removal,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (28772)------------------------------
% 1.31/0.54  % (28772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (28772)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (28772)Memory used [KB]: 1918
% 1.31/0.54  % (28772)Time elapsed: 0.113 s
% 1.31/0.54  % (28772)------------------------------
% 1.31/0.54  % (28772)------------------------------
% 1.31/0.54  % (28742)Success in time 0.176 s
%------------------------------------------------------------------------------
