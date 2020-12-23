%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:04 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 519 expanded)
%              Number of leaves         :   14 ( 130 expanded)
%              Depth                    :   22
%              Number of atoms          :  392 (2623 expanded)
%              Number of equality atoms :  165 ( 985 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2039,plain,(
    $false ),
    inference(equality_resolution,[],[f1995])).

% (30453)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% (30391)Refutation not found, incomplete strategy% (30391)------------------------------
% (30391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30391)Termination reason: Refutation not found, incomplete strategy

% (30391)Memory used [KB]: 1918
% (30391)Time elapsed: 0.264 s
% (30391)------------------------------
% (30391)------------------------------
fof(f1995,plain,(
    ! [X12] : sK1 != X12 ),
    inference(resolution,[],[f1967,f396])).

fof(f396,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f100,f384])).

fof(f384,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f382,f58])).

fof(f58,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f30])).

fof(f30,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f382,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f373,f234])).

fof(f234,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f231,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f231,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f227,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f227,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f223,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f223,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f81,f57])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f373,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f363,f120])).

fof(f120,plain,(
    v5_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f80,f57])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f363,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,k1_tarski(X0))
      | sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f362,f119])).

fof(f119,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f362,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f353,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f353,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_funct_1(sK3)
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(superposition,[],[f59,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X0) = X2
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,k1_tarski(X2))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f68,f101])).

fof(f101,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f59,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1967,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | sK1 != X8 ) ),
    inference(subsumption_resolution,[],[f1941,f1940])).

fof(f1940,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,X3)
      | sK1 != X5 ) ),
    inference(superposition,[],[f108,f1715])).

fof(f1715,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k4_xboole_0(X4,X4)
      | sK1 != X3 ) ),
    inference(duplicate_literal_removal,[],[f1652])).

fof(f1652,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k4_xboole_0(X4,X4)
      | k1_xboole_0 = k4_xboole_0(X4,X4)
      | sK1 != X3 ) ),
    inference(superposition,[],[f432,f383])).

fof(f383,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k1_xboole_0
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f381,f58])).

fof(f381,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,sK0)
      | k1_tarski(X0) = k1_xboole_0
      | sK1 != X0 ) ),
    inference(superposition,[],[f373,f261])).

fof(f261,plain,(
    ! [X1] :
      ( sK0 = k1_relat_1(sK3)
      | k1_tarski(X1) = k1_xboole_0
      | sK1 != X1 ) ),
    inference(subsumption_resolution,[],[f258,f176])).

fof(f176,plain,(
    ! [X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(X1))))
      | k1_tarski(X1) = k1_xboole_0
      | sK1 != X1 ) ),
    inference(superposition,[],[f57,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_xboole_0
      | X0 != X1 ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f74,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( sK6(k1_tarski(X0),X1) = X0
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f73,f101])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f258,plain,(
    ! [X1] :
      ( sK0 = k1_relat_1(sK3)
      | k1_tarski(X1) = k1_xboole_0
      | sK1 != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(X1)))) ) ),
    inference(superposition,[],[f228,f79])).

fof(f228,plain,(
    ! [X0] :
      ( sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3)
      | k1_tarski(X0) = k1_xboole_0
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f226,f177])).

fof(f177,plain,(
    ! [X2] :
      ( v1_funct_2(sK3,sK0,k1_tarski(X2))
      | k1_xboole_0 = k1_tarski(X2)
      | sK1 != X2 ) ),
    inference(superposition,[],[f56,f155])).

fof(f226,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK0,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3)
      | sK1 != X0 ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK0,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3)
      | k1_tarski(X0) = k1_xboole_0
      | sK1 != X0 ) ),
    inference(resolution,[],[f81,f176])).

fof(f432,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_tarski(X1) = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f129,f128])).

fof(f128,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(k4_xboole_0(X2,X3),X4),X2)
      | k4_xboole_0(X2,X3) = k1_tarski(X4)
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f73,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f129,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK6(k4_xboole_0(X5,X6),X7),X6)
      | k4_xboole_0(X5,X6) = k1_tarski(X7)
      | k1_xboole_0 = k4_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f73,f108])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1941,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(X7,X6)
      | sK1 != X8 ) ),
    inference(superposition,[],[f109,f1715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (30398)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (30400)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (30410)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (30408)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (30393)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (30406)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (30395)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (30394)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (30392)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (30392)Refutation not found, incomplete strategy% (30392)------------------------------
% 0.21/0.53  % (30392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30392)Memory used [KB]: 1663
% 0.21/0.53  % (30392)Time elapsed: 0.102 s
% 0.21/0.53  % (30392)------------------------------
% 0.21/0.53  % (30392)------------------------------
% 0.21/0.53  % (30391)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (30414)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (30420)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (30396)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (30420)Refutation not found, incomplete strategy% (30420)------------------------------
% 0.21/0.54  % (30420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30420)Memory used [KB]: 1663
% 0.21/0.54  % (30420)Time elapsed: 0.136 s
% 0.21/0.54  % (30420)------------------------------
% 0.21/0.54  % (30420)------------------------------
% 0.21/0.54  % (30397)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (30399)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (30409)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (30401)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (30407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (30403)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (30402)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (30405)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (30416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (30413)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (30417)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (30407)Refutation not found, incomplete strategy% (30407)------------------------------
% 0.21/0.56  % (30407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30407)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30407)Memory used [KB]: 10746
% 0.21/0.56  % (30407)Time elapsed: 0.152 s
% 0.21/0.56  % (30407)------------------------------
% 0.21/0.56  % (30407)------------------------------
% 0.21/0.56  % (30419)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (30412)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (30411)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (30418)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (30418)Refutation not found, incomplete strategy% (30418)------------------------------
% 0.21/0.57  % (30418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (30418)Memory used [KB]: 6396
% 0.21/0.57  % (30418)Time elapsed: 0.133 s
% 0.21/0.57  % (30418)------------------------------
% 0.21/0.57  % (30418)------------------------------
% 0.21/0.58  % (30404)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.82/0.59  % (30415)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.14/0.66  % (30452)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.67  % (30455)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.14/0.68  % (30455)Refutation not found, incomplete strategy% (30455)------------------------------
% 2.14/0.68  % (30455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (30455)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (30455)Memory used [KB]: 6268
% 2.14/0.68  % (30455)Time elapsed: 0.059 s
% 2.14/0.68  % (30455)------------------------------
% 2.14/0.68  % (30455)------------------------------
% 2.14/0.69  % (30400)Refutation found. Thanks to Tanya!
% 2.14/0.69  % SZS status Theorem for theBenchmark
% 2.14/0.69  % SZS output start Proof for theBenchmark
% 2.14/0.69  fof(f2039,plain,(
% 2.14/0.69    $false),
% 2.14/0.69    inference(equality_resolution,[],[f1995])).
% 2.14/0.69  % (30453)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.14/0.69  % (30391)Refutation not found, incomplete strategy% (30391)------------------------------
% 2.14/0.69  % (30391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (30391)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.69  
% 2.14/0.69  % (30391)Memory used [KB]: 1918
% 2.14/0.69  % (30391)Time elapsed: 0.264 s
% 2.14/0.69  % (30391)------------------------------
% 2.14/0.69  % (30391)------------------------------
% 2.14/0.71  fof(f1995,plain,(
% 2.14/0.71    ( ! [X12] : (sK1 != X12) )),
% 2.14/0.71    inference(resolution,[],[f1967,f396])).
% 2.14/0.71  fof(f396,plain,(
% 2.14/0.71    r2_hidden(sK1,k1_xboole_0)),
% 2.14/0.71    inference(superposition,[],[f100,f384])).
% 2.14/0.71  fof(f384,plain,(
% 2.14/0.71    k1_xboole_0 = k1_tarski(sK1)),
% 2.14/0.71    inference(subsumption_resolution,[],[f382,f58])).
% 2.14/0.71  fof(f58,plain,(
% 2.14/0.71    r2_hidden(sK2,sK0)),
% 2.14/0.71    inference(cnf_transformation,[],[f31])).
% 2.14/0.71  fof(f31,plain,(
% 2.14/0.71    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 2.14/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f30])).
% 2.14/0.71  fof(f30,plain,(
% 2.14/0.71    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 2.14/0.71    introduced(choice_axiom,[])).
% 2.14/0.71  fof(f19,plain,(
% 2.14/0.71    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.14/0.71    inference(flattening,[],[f18])).
% 2.14/0.71  fof(f18,plain,(
% 2.14/0.71    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.14/0.71    inference(ennf_transformation,[],[f16])).
% 2.14/0.71  fof(f16,negated_conjecture,(
% 2.14/0.71    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.14/0.71    inference(negated_conjecture,[],[f15])).
% 2.14/0.71  fof(f15,conjecture,(
% 2.14/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 2.14/0.71  fof(f382,plain,(
% 2.14/0.71    ~r2_hidden(sK2,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 2.14/0.71    inference(superposition,[],[f373,f234])).
% 2.14/0.71  fof(f234,plain,(
% 2.14/0.71    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 2.14/0.71    inference(subsumption_resolution,[],[f231,f57])).
% 2.14/0.71  fof(f57,plain,(
% 2.14/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.14/0.71    inference(cnf_transformation,[],[f31])).
% 2.14/0.71  fof(f231,plain,(
% 2.14/0.71    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.14/0.71    inference(superposition,[],[f227,f79])).
% 2.14/0.71  fof(f79,plain,(
% 2.14/0.71    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.71    inference(cnf_transformation,[],[f26])).
% 2.14/0.71  fof(f26,plain,(
% 2.14/0.71    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.71    inference(ennf_transformation,[],[f12])).
% 2.14/0.71  fof(f12,axiom,(
% 2.14/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.14/0.71  fof(f227,plain,(
% 2.14/0.71    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 2.14/0.71    inference(subsumption_resolution,[],[f223,f56])).
% 2.14/0.71  fof(f56,plain,(
% 2.14/0.71    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.14/0.71    inference(cnf_transformation,[],[f31])).
% 2.14/0.71  fof(f223,plain,(
% 2.14/0.71    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 2.14/0.71    inference(resolution,[],[f81,f57])).
% 2.14/0.71  fof(f81,plain,(
% 2.14/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.14/0.71    inference(cnf_transformation,[],[f44])).
% 2.14/0.71  fof(f44,plain,(
% 2.14/0.71    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.71    inference(nnf_transformation,[],[f29])).
% 2.14/0.71  fof(f29,plain,(
% 2.14/0.71    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.71    inference(flattening,[],[f28])).
% 2.14/0.71  fof(f28,plain,(
% 2.14/0.71    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.71    inference(ennf_transformation,[],[f14])).
% 2.14/0.71  fof(f14,axiom,(
% 2.14/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.14/0.71  fof(f373,plain,(
% 2.14/0.71    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 2.14/0.71    inference(trivial_inequality_removal,[],[f364])).
% 2.14/0.71  fof(f364,plain,(
% 2.14/0.71    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 2.14/0.71    inference(resolution,[],[f363,f120])).
% 2.14/0.71  fof(f120,plain,(
% 2.14/0.71    v5_relat_1(sK3,k1_tarski(sK1))),
% 2.14/0.71    inference(resolution,[],[f80,f57])).
% 2.14/0.71  fof(f80,plain,(
% 2.14/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.14/0.71    inference(cnf_transformation,[],[f27])).
% 2.14/0.71  fof(f27,plain,(
% 2.14/0.71    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.71    inference(ennf_transformation,[],[f17])).
% 2.14/0.71  fof(f17,plain,(
% 2.14/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.14/0.71    inference(pure_predicate_removal,[],[f11])).
% 2.14/0.71  fof(f11,axiom,(
% 2.14/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.14/0.71  fof(f363,plain,(
% 2.14/0.71    ( ! [X0] : (~v5_relat_1(sK3,k1_tarski(X0)) | sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f362,f119])).
% 2.14/0.71  fof(f119,plain,(
% 2.14/0.71    v1_relat_1(sK3)),
% 2.14/0.71    inference(subsumption_resolution,[],[f118,f66])).
% 2.14/0.71  fof(f66,plain,(
% 2.14/0.71    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.14/0.71    inference(cnf_transformation,[],[f8])).
% 2.14/0.71  fof(f8,axiom,(
% 2.14/0.71    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.14/0.71  fof(f118,plain,(
% 2.14/0.71    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 2.14/0.71    inference(resolution,[],[f61,f57])).
% 2.14/0.71  fof(f61,plain,(
% 2.14/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.71    inference(cnf_transformation,[],[f20])).
% 2.14/0.71  fof(f20,plain,(
% 2.14/0.71    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.14/0.71    inference(ennf_transformation,[],[f7])).
% 2.14/0.71  fof(f7,axiom,(
% 2.14/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.14/0.71  fof(f362,plain,(
% 2.14/0.71    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f353,f55])).
% 2.14/0.71  fof(f55,plain,(
% 2.14/0.71    v1_funct_1(sK3)),
% 2.14/0.71    inference(cnf_transformation,[],[f31])).
% 2.14/0.71  fof(f353,plain,(
% 2.14/0.71    ( ! [X0] : (sK1 != X0 | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 2.14/0.71    inference(superposition,[],[f59,f156])).
% 2.14/0.71  fof(f156,plain,(
% 2.14/0.71    ( ! [X2,X0,X1] : (k1_funct_1(X1,X0) = X2 | ~v1_funct_1(X1) | ~v5_relat_1(X1,k1_tarski(X2)) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 2.14/0.71    inference(resolution,[],[f68,f101])).
% 2.14/0.71  fof(f101,plain,(
% 2.14/0.71    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.14/0.71    inference(equality_resolution,[],[f69])).
% 2.14/0.71  fof(f69,plain,(
% 2.14/0.71    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.14/0.71    inference(cnf_transformation,[],[f37])).
% 2.14/0.71  fof(f37,plain,(
% 2.14/0.71    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 2.14/0.71  fof(f36,plain,(
% 2.14/0.71    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.14/0.71    introduced(choice_axiom,[])).
% 2.14/0.71  fof(f35,plain,(
% 2.14/0.71    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.71    inference(rectify,[],[f34])).
% 2.14/0.71  fof(f34,plain,(
% 2.14/0.71    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.71    inference(nnf_transformation,[],[f2])).
% 2.14/0.71  fof(f2,axiom,(
% 2.14/0.71    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.14/0.71  fof(f68,plain,(
% 2.14/0.71    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.14/0.71    inference(cnf_transformation,[],[f23])).
% 2.14/0.71  fof(f23,plain,(
% 2.14/0.71    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.71    inference(flattening,[],[f22])).
% 2.14/0.71  fof(f22,plain,(
% 2.14/0.71    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.14/0.71    inference(ennf_transformation,[],[f10])).
% 2.14/0.71  fof(f10,axiom,(
% 2.14/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 2.14/0.71  fof(f59,plain,(
% 2.14/0.71    sK1 != k1_funct_1(sK3,sK2)),
% 2.14/0.71    inference(cnf_transformation,[],[f31])).
% 2.14/0.71  fof(f100,plain,(
% 2.14/0.71    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.14/0.71    inference(equality_resolution,[],[f99])).
% 2.14/0.71  fof(f99,plain,(
% 2.14/0.71    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.14/0.71    inference(equality_resolution,[],[f70])).
% 2.14/0.71  fof(f70,plain,(
% 2.14/0.71    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.14/0.71    inference(cnf_transformation,[],[f37])).
% 2.14/0.71  fof(f1967,plain,(
% 2.14/0.71    ( ! [X8,X7] : (~r2_hidden(X7,k1_xboole_0) | sK1 != X8) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f1941,f1940])).
% 2.14/0.71  fof(f1940,plain,(
% 2.14/0.71    ( ! [X4,X5,X3] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,X3) | sK1 != X5) )),
% 2.14/0.71    inference(superposition,[],[f108,f1715])).
% 2.14/0.71  fof(f1715,plain,(
% 2.14/0.71    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X4,X4) | sK1 != X3) )),
% 2.14/0.71    inference(duplicate_literal_removal,[],[f1652])).
% 2.14/0.71  fof(f1652,plain,(
% 2.14/0.71    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X4,X4) | k1_xboole_0 = k4_xboole_0(X4,X4) | sK1 != X3) )),
% 2.14/0.71    inference(superposition,[],[f432,f383])).
% 2.14/0.71  fof(f383,plain,(
% 2.14/0.71    ( ! [X0] : (k1_tarski(X0) = k1_xboole_0 | sK1 != X0) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f381,f58])).
% 2.14/0.71  fof(f381,plain,(
% 2.14/0.71    ( ! [X0] : (~r2_hidden(sK2,sK0) | k1_tarski(X0) = k1_xboole_0 | sK1 != X0) )),
% 2.14/0.71    inference(superposition,[],[f373,f261])).
% 2.14/0.71  fof(f261,plain,(
% 2.14/0.71    ( ! [X1] : (sK0 = k1_relat_1(sK3) | k1_tarski(X1) = k1_xboole_0 | sK1 != X1) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f258,f176])).
% 2.14/0.71  fof(f176,plain,(
% 2.14/0.71    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(X1)))) | k1_tarski(X1) = k1_xboole_0 | sK1 != X1) )),
% 2.14/0.71    inference(superposition,[],[f57,f155])).
% 2.14/0.71  fof(f155,plain,(
% 2.14/0.71    ( ! [X0,X1] : (k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_xboole_0 | X0 != X1) )),
% 2.14/0.71    inference(duplicate_literal_removal,[],[f152])).
% 2.14/0.71  fof(f152,plain,(
% 2.14/0.71    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_xboole_0) )),
% 2.14/0.71    inference(superposition,[],[f74,f127])).
% 2.14/0.71  fof(f127,plain,(
% 2.14/0.71    ( ! [X0,X1] : (sK6(k1_tarski(X0),X1) = X0 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_xboole_0) )),
% 2.14/0.71    inference(resolution,[],[f73,f101])).
% 2.14/0.71  fof(f73,plain,(
% 2.14/0.71    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.14/0.71    inference(cnf_transformation,[],[f39])).
% 2.14/0.71  fof(f39,plain,(
% 2.14/0.71    ! [X0,X1] : ((sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.14/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f38])).
% 2.14/0.71  fof(f38,plain,(
% 2.14/0.71    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)))),
% 2.14/0.71    introduced(choice_axiom,[])).
% 2.14/0.71  fof(f24,plain,(
% 2.14/0.71    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.14/0.71    inference(ennf_transformation,[],[f6])).
% 2.14/0.71  fof(f6,axiom,(
% 2.14/0.71    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 2.14/0.71  fof(f74,plain,(
% 2.14/0.71    ( ! [X0,X1] : (sK6(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.14/0.71    inference(cnf_transformation,[],[f39])).
% 2.14/0.71  fof(f258,plain,(
% 2.14/0.71    ( ! [X1] : (sK0 = k1_relat_1(sK3) | k1_tarski(X1) = k1_xboole_0 | sK1 != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(X1))))) )),
% 2.14/0.71    inference(superposition,[],[f228,f79])).
% 2.14/0.71  fof(f228,plain,(
% 2.14/0.71    ( ! [X0] : (sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3) | k1_tarski(X0) = k1_xboole_0 | sK1 != X0) )),
% 2.14/0.71    inference(subsumption_resolution,[],[f226,f177])).
% 2.14/0.71  fof(f177,plain,(
% 2.14/0.71    ( ! [X2] : (v1_funct_2(sK3,sK0,k1_tarski(X2)) | k1_xboole_0 = k1_tarski(X2) | sK1 != X2) )),
% 2.14/0.71    inference(superposition,[],[f56,f155])).
% 2.14/0.71  fof(f226,plain,(
% 2.14/0.71    ( ! [X0] : (~v1_funct_2(sK3,sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3) | sK1 != X0) )),
% 2.14/0.71    inference(duplicate_literal_removal,[],[f224])).
% 2.14/0.71  fof(f224,plain,(
% 2.14/0.71    ( ! [X0] : (~v1_funct_2(sK3,sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | sK0 = k1_relset_1(sK0,k1_tarski(X0),sK3) | k1_tarski(X0) = k1_xboole_0 | sK1 != X0) )),
% 2.14/0.71    inference(resolution,[],[f81,f176])).
% 2.14/0.71  fof(f432,plain,(
% 2.14/0.71    ( ! [X0,X1] : (k1_tarski(X1) = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.14/0.71    inference(duplicate_literal_removal,[],[f429])).
% 2.14/0.71  fof(f429,plain,(
% 2.14/0.71    ( ! [X0,X1] : (k1_tarski(X1) = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0) | k1_tarski(X1) = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.14/0.71    inference(resolution,[],[f129,f128])).
% 2.14/0.71  fof(f128,plain,(
% 2.14/0.71    ( ! [X4,X2,X3] : (r2_hidden(sK6(k4_xboole_0(X2,X3),X4),X2) | k4_xboole_0(X2,X3) = k1_tarski(X4) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 2.14/0.71    inference(resolution,[],[f73,f109])).
% 2.14/0.71  fof(f109,plain,(
% 2.14/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.14/0.71    inference(equality_resolution,[],[f87])).
% 2.14/0.71  fof(f87,plain,(
% 2.14/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.14/0.71    inference(cnf_transformation,[],[f49])).
% 2.14/0.71  fof(f49,plain,(
% 2.14/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.14/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).
% 2.14/0.71  fof(f48,plain,(
% 2.14/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.14/0.71    introduced(choice_axiom,[])).
% 2.14/0.71  fof(f47,plain,(
% 2.14/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.14/0.71    inference(rectify,[],[f46])).
% 2.14/0.71  fof(f46,plain,(
% 2.14/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.14/0.71    inference(flattening,[],[f45])).
% 2.14/0.71  fof(f45,plain,(
% 2.14/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.14/0.71    inference(nnf_transformation,[],[f1])).
% 2.14/0.71  fof(f1,axiom,(
% 2.14/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.14/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.14/0.71  fof(f129,plain,(
% 2.14/0.71    ( ! [X6,X7,X5] : (~r2_hidden(sK6(k4_xboole_0(X5,X6),X7),X6) | k4_xboole_0(X5,X6) = k1_tarski(X7) | k1_xboole_0 = k4_xboole_0(X5,X6)) )),
% 2.14/0.71    inference(resolution,[],[f73,f108])).
% 2.14/0.71  fof(f108,plain,(
% 2.14/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.14/0.71    inference(equality_resolution,[],[f88])).
% 2.14/0.71  fof(f88,plain,(
% 2.14/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.14/0.71    inference(cnf_transformation,[],[f49])).
% 2.14/0.71  fof(f1941,plain,(
% 2.14/0.71    ( ! [X6,X8,X7] : (~r2_hidden(X7,k1_xboole_0) | r2_hidden(X7,X6) | sK1 != X8) )),
% 2.14/0.71    inference(superposition,[],[f109,f1715])).
% 2.14/0.71  % SZS output end Proof for theBenchmark
% 2.14/0.71  % (30400)------------------------------
% 2.14/0.71  % (30400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.71  % (30400)Termination reason: Refutation
% 2.14/0.71  
% 2.14/0.71  % (30400)Memory used [KB]: 3198
% 2.14/0.71  % (30400)Time elapsed: 0.275 s
% 2.14/0.71  % (30400)------------------------------
% 2.14/0.71  % (30400)------------------------------
% 2.14/0.72  % (30390)Success in time 0.36 s
%------------------------------------------------------------------------------
