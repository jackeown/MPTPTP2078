%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:46 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  159 (4648 expanded)
%              Number of leaves         :   17 (1394 expanded)
%              Depth                    :   48
%              Number of atoms          :  603 (38839 expanded)
%              Number of equality atoms :  163 (1750 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f890,plain,(
    $false ),
    inference(resolution,[],[f889,f97])).

fof(f97,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f84,f95])).

fof(f95,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f92,f84])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ) ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f91,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f74,f83])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f79,f62])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f889,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f841,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f841,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f688,f826])).

fof(f826,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f820,f97])).

fof(f820,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k2_funct_1(k1_xboole_0) ) ),
    inference(resolution,[],[f819,f63])).

fof(f819,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f817,f587])).

fof(f587,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f586])).

fof(f586,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f519,f404])).

fof(f404,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f53,f398])).

fof(f398,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f393,f53])).

fof(f393,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f359,f87])).

fof(f359,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f160,f358])).

fof(f358,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f357,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f357,plain,
    ( ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(resolution,[],[f356,f50])).

fof(f356,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(resolution,[],[f355,f48])).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f355,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f353,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f353,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_xboole_0 = sK0
      | sK2 = k2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v3_funct_2(sK1,X3,X4)
      | ~ v1_funct_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(sK2)
      | k1_xboole_0 = sK0
      | sK2 = k2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v3_funct_2(sK1,X3,X4)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f350,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

% (10482)Refutation not found, incomplete strategy% (10482)------------------------------
% (10482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10482)Termination reason: Refutation not found, incomplete strategy

% (10482)Memory used [KB]: 1791
% (10482)Time elapsed: 0.162 s
% (10482)------------------------------
% (10482)------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f350,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f295,f47])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f295,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f292,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f292,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v2_funct_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f269,f49])).

fof(f269,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = k2_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f268,f53])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f261,f54])).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f261,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f256])).

fof(f256,plain,(
    ! [X0] :
      ( sK0 != sK0
      | k1_xboole_0 = sK0
      | ~ v2_funct_1(sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(backward_demodulation,[],[f149,f249])).

fof(f249,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f247,f49])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f246,f63])).

fof(f246,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f244,f46])).

fof(f244,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f225,f49])).

fof(f225,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f222,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f222,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f199,f48])).

fof(f199,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f115,f49])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | k2_relat_1(X0) = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f149,plain,(
    ! [X0] :
      ( sK0 != k2_relat_1(sK1)
      | k1_xboole_0 = sK0
      | ~ v2_funct_1(sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( sK0 != k2_relat_1(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | ~ v2_funct_1(sK1)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0))
      | k2_funct_1(sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(superposition,[],[f59,f105])).

fof(f105,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_funct_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f160,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f55,f159])).

fof(f159,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f157,f46])).

fof(f157,plain,
    ( ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f156,f48])).

fof(f156,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f56,f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f55,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f519,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f450,f63])).

fof(f450,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f435])).

fof(f435,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f284,f398])).

fof(f284,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f75,f278])).

fof(f278,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f277,f53])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f271,f63])).

fof(f271,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f270,f50])).

fof(f270,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f226,f53])).

fof(f226,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | sK0 = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f224,f81])).

fof(f224,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | sK0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f200,f52])).

fof(f52,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f200,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f115,f53])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f817,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f816,f594])).

fof(f594,plain,(
    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f403,f586])).

fof(f403,plain,(
    v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f398])).

fof(f816,plain,
    ( ~ v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f747,f97])).

fof(f747,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v3_funct_2(k1_xboole_0,X3,X4)
      | k1_xboole_0 = k2_funct_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f746])).

fof(f746,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v3_funct_2(k1_xboole_0,X3,X4)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f664,f65])).

fof(f664,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f622,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f622,plain,
    ( ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f621,f586])).

fof(f621,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f620])).

fof(f620,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f619,f98])).

fof(f98,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f83,f95])).

fof(f619,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f590,f586])).

fof(f590,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f232,f586])).

fof(f232,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f75,f230])).

fof(f230,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f223,f53])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f221,f63])).

fof(f221,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f219,f50])).

% (10485)Refutation not found, incomplete strategy% (10485)------------------------------
% (10485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f219,plain,
    ( ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f193,f52])).

% (10485)Termination reason: Refutation not found, incomplete strategy

% (10485)Memory used [KB]: 1791
% (10485)Time elapsed: 0.162 s
% (10485)------------------------------
% (10485)------------------------------
fof(f193,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f112,f53])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f65,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f688,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f598,f666])).

fof(f666,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f529,f401])).

fof(f401,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f49,f398])).

fof(f529,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f452,f63])).

fof(f452,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f426])).

fof(f426,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f260,f398])).

fof(f260,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f75,f249])).

fof(f598,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f418,f586])).

fof(f418,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f160,f398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (10492)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (10483)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (10473)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (10477)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (10490)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (10476)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (10481)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (10472)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (10496)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (10469)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (10470)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (10474)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10468)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (10471)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (10489)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (10486)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (10485)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (10480)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (10491)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (10484)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (10479)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (10498)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (10475)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (10494)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (10497)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (10478)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (10493)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (10496)Refutation not found, incomplete strategy% (10496)------------------------------
% 0.20/0.55  % (10496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10496)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10496)Memory used [KB]: 6396
% 0.20/0.55  % (10496)Time elapsed: 0.139 s
% 0.20/0.55  % (10496)------------------------------
% 0.20/0.55  % (10496)------------------------------
% 0.20/0.55  % (10493)Refutation not found, incomplete strategy% (10493)------------------------------
% 0.20/0.55  % (10493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10493)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10493)Memory used [KB]: 10746
% 0.20/0.55  % (10493)Time elapsed: 0.152 s
% 0.20/0.55  % (10493)------------------------------
% 0.20/0.55  % (10493)------------------------------
% 0.20/0.55  % (10487)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.55  % (10495)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.45/0.56  % (10473)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % (10484)Refutation not found, incomplete strategy% (10484)------------------------------
% 1.45/0.56  % (10484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10484)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10484)Memory used [KB]: 10746
% 1.45/0.56  % (10484)Time elapsed: 0.143 s
% 1.45/0.56  % (10484)------------------------------
% 1.45/0.56  % (10484)------------------------------
% 1.45/0.56  % (10482)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f890,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(resolution,[],[f889,f97])).
% 1.45/0.56  fof(f97,plain,(
% 1.45/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.45/0.56    inference(superposition,[],[f84,f95])).
% 1.45/0.56  fof(f95,plain,(
% 1.45/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f92,f84])).
% 1.45/0.56  fof(f92,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k6_partfun1(k1_xboole_0)) )),
% 1.45/0.56    inference(resolution,[],[f91,f63])).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.45/0.56  fof(f91,plain,(
% 1.45/0.56    ~v1_relat_1(k6_partfun1(k1_xboole_0)) | k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.45/0.56    inference(equality_resolution,[],[f88])).
% 1.45/0.56  fof(f88,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.45/0.56    inference(superposition,[],[f74,f83])).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.45/0.56    inference(definition_unfolding,[],[f72,f62])).
% 1.45/0.56  fof(f62,plain,(
% 1.45/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,axiom,(
% 1.45/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.45/0.56  fof(f74,plain,(
% 1.45/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f35])).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.45/0.56  fof(f84,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f79,f62])).
% 1.45/0.56  fof(f79,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.45/0.56  fof(f889,plain,(
% 1.45/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.45/0.56    inference(resolution,[],[f841,f87])).
% 1.45/0.56  fof(f87,plain,(
% 1.45/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f85])).
% 1.45/0.56  fof(f85,plain,(
% 1.45/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(equality_resolution,[],[f58])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(nnf_transformation,[],[f23])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(flattening,[],[f22])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.45/0.56  fof(f841,plain,(
% 1.45/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.45/0.56    inference(backward_demodulation,[],[f688,f826])).
% 1.45/0.56  fof(f826,plain,(
% 1.45/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f820,f97])).
% 1.45/0.56  fof(f820,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k2_funct_1(k1_xboole_0)) )),
% 1.45/0.56    inference(resolution,[],[f819,f63])).
% 1.45/0.56  fof(f819,plain,(
% 1.45/0.56    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f817,f587])).
% 1.45/0.56  fof(f587,plain,(
% 1.45/0.56    v1_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(backward_demodulation,[],[f50,f586])).
% 1.45/0.56  fof(f586,plain,(
% 1.45/0.56    k1_xboole_0 = sK2),
% 1.45/0.56    inference(resolution,[],[f519,f404])).
% 1.45/0.56  fof(f404,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.45/0.56    inference(backward_demodulation,[],[f53,f398])).
% 1.45/0.56  fof(f398,plain,(
% 1.45/0.56    k1_xboole_0 = sK0),
% 1.45/0.56    inference(resolution,[],[f393,f53])).
% 1.45/0.56  fof(f393,plain,(
% 1.45/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0),
% 1.45/0.56    inference(resolution,[],[f359,f87])).
% 1.45/0.56  fof(f359,plain,(
% 1.45/0.56    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 1.45/0.56    inference(superposition,[],[f160,f358])).
% 1.45/0.56  fof(f358,plain,(
% 1.45/0.56    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 1.45/0.56    inference(resolution,[],[f357,f46])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    v1_funct_1(sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f42,f41])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f42,plain,(
% 1.45/0.56    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f19,plain,(
% 1.45/0.56    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.45/0.56    inference(flattening,[],[f18])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.45/0.56    inference(negated_conjecture,[],[f16])).
% 1.45/0.56  fof(f16,conjecture,(
% 1.45/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.45/0.56  fof(f357,plain,(
% 1.45/0.56    ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f356,f50])).
% 1.45/0.56  fof(f356,plain,(
% 1.45/0.56    ~v1_funct_1(sK2) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f355,f48])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    v3_funct_2(sK1,sK0,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f355,plain,(
% 1.45/0.56    ~v3_funct_2(sK1,sK0,sK0) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f353,f49])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f353,plain,(
% 1.45/0.56    ( ! [X4,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v3_funct_2(sK1,X3,X4) | ~v1_funct_1(sK2)) )),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f352])).
% 1.45/0.56  fof(f352,plain,(
% 1.45/0.56    ( ! [X4,X3] : (~v1_funct_1(sK2) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v3_funct_2(sK1,X3,X4) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.45/0.56    inference(resolution,[],[f350,f65])).
% 1.45/0.56  fof(f65,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f30])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(flattening,[],[f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f10])).
% 1.45/0.56  % (10482)Refutation not found, incomplete strategy% (10482)------------------------------
% 1.45/0.56  % (10482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10482)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10482)Memory used [KB]: 1791
% 1.45/0.56  % (10482)Time elapsed: 0.162 s
% 1.45/0.56  % (10482)------------------------------
% 1.45/0.56  % (10482)------------------------------
% 1.45/0.56  fof(f10,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.45/0.56  fof(f350,plain,(
% 1.45/0.56    ~v2_funct_1(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f295,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f295,plain,(
% 1.45/0.56    ~v1_funct_2(sK1,sK0,sK0) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f292,f51])).
% 1.45/0.56  fof(f51,plain,(
% 1.45/0.56    v1_funct_2(sK2,sK0,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f292,plain,(
% 1.45/0.56    ~v1_funct_2(sK2,sK0,sK0) | ~v2_funct_1(sK1) | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f269,f49])).
% 1.45/0.56  fof(f269,plain,(
% 1.45/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = k2_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f268,f53])).
% 1.45/0.56  fof(f268,plain,(
% 1.45/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f261,f54])).
% 1.45/0.56  fof(f54,plain,(
% 1.45/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f261,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f256])).
% 1.45/0.56  fof(f256,plain,(
% 1.45/0.56    ( ! [X0] : (sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.45/0.56    inference(backward_demodulation,[],[f149,f249])).
% 1.45/0.56  fof(f249,plain,(
% 1.45/0.56    sK0 = k2_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f247,f49])).
% 1.45/0.56  fof(f247,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(sK1)) )),
% 1.45/0.56    inference(resolution,[],[f246,f63])).
% 1.45/0.56  fof(f246,plain,(
% 1.45/0.56    ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f244,f46])).
% 1.45/0.56  fof(f244,plain,(
% 1.45/0.56    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f225,f49])).
% 1.45/0.56  fof(f225,plain,(
% 1.45/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)) )),
% 1.45/0.56    inference(resolution,[],[f222,f81])).
% 1.45/0.56  fof(f81,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f40])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.45/0.56  fof(f222,plain,(
% 1.45/0.56    ~v5_relat_1(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f199,f48])).
% 1.45/0.56  fof(f199,plain,(
% 1.45/0.56    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f115,f49])).
% 1.45/0.56  fof(f115,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v3_funct_2(X0,X1,X2) | k2_relat_1(X0) = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(resolution,[],[f66,f77])).
% 1.45/0.56  fof(f77,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(nnf_transformation,[],[f39])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(flattening,[],[f38])).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,axiom,(
% 1.45/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.45/0.56  fof(f66,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f30])).
% 1.45/0.56  fof(f149,plain,(
% 1.45/0.56    ( ! [X0] : (sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f145])).
% 1.45/0.56  fof(f145,plain,(
% 1.45/0.56    ( ! [X0] : (sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0),k6_partfun1(sK0)) | k2_funct_1(sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.45/0.56    inference(superposition,[],[f59,f105])).
% 1.45/0.56  fof(f105,plain,(
% 1.45/0.56    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f76,f49])).
% 1.45/0.56  fof(f76,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f37])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_funct_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.56    inference(flattening,[],[f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.56    inference(ennf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.45/0.56  fof(f160,plain,(
% 1.45/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.45/0.56    inference(backward_demodulation,[],[f55,f159])).
% 1.45/0.56  fof(f159,plain,(
% 1.45/0.56    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f157,f46])).
% 1.45/0.56  fof(f157,plain,(
% 1.45/0.56    ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f156,f48])).
% 1.45/0.56  fof(f156,plain,(
% 1.45/0.56    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f133,f47])).
% 1.45/0.56  fof(f133,plain,(
% 1.45/0.56    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.45/0.56    inference(resolution,[],[f56,f49])).
% 1.45/0.56  fof(f56,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.45/0.56    inference(flattening,[],[f20])).
% 1.45/0.56  fof(f20,plain,(
% 1.45/0.56    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,axiom,(
% 1.45/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.45/0.56  fof(f55,plain,(
% 1.45/0.56    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f519,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 1.45/0.56    inference(resolution,[],[f450,f63])).
% 1.45/0.56  fof(f450,plain,(
% 1.45/0.56    ~v1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f435])).
% 1.45/0.56  fof(f435,plain,(
% 1.45/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f284,f398])).
% 1.45/0.56  fof(f284,plain,(
% 1.45/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(superposition,[],[f75,f278])).
% 1.45/0.56  fof(f278,plain,(
% 1.45/0.56    sK0 = k2_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f277,f53])).
% 1.45/0.56  fof(f277,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(sK2)) )),
% 1.45/0.56    inference(resolution,[],[f271,f63])).
% 1.45/0.56  fof(f271,plain,(
% 1.45/0.56    ~v1_relat_1(sK2) | sK0 = k2_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f270,f50])).
% 1.45/0.56  fof(f270,plain,(
% 1.45/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = k2_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f226,f53])).
% 1.45/0.56  fof(f226,plain,(
% 1.45/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = k2_relat_1(sK2)) )),
% 1.45/0.56    inference(resolution,[],[f224,f81])).
% 1.45/0.56  fof(f224,plain,(
% 1.45/0.56    ~v5_relat_1(sK2,sK0) | sK0 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f200,f52])).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    v3_funct_2(sK2,sK0,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f200,plain,(
% 1.45/0.56    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f115,f53])).
% 1.45/0.56  fof(f75,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    v1_funct_1(sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f43])).
% 1.45/0.56  fof(f817,plain,(
% 1.45/0.56    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f816,f594])).
% 1.45/0.56  fof(f594,plain,(
% 1.45/0.56    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.45/0.56    inference(backward_demodulation,[],[f403,f586])).
% 1.45/0.56  fof(f403,plain,(
% 1.45/0.56    v3_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.45/0.56    inference(backward_demodulation,[],[f52,f398])).
% 1.45/0.56  fof(f816,plain,(
% 1.45/0.56    ~v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f747,f97])).
% 1.45/0.56  fof(f747,plain,(
% 1.45/0.56    ( ! [X4,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v3_funct_2(k1_xboole_0,X3,X4) | k1_xboole_0 = k2_funct_1(k1_xboole_0)) )),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f746])).
% 1.45/0.56  fof(f746,plain,(
% 1.45/0.56    ( ! [X4,X3] : (k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v3_funct_2(k1_xboole_0,X3,X4) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.45/0.56    inference(resolution,[],[f664,f65])).
% 1.45/0.56  fof(f664,plain,(
% 1.45/0.56    ~v2_funct_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.45/0.56    inference(resolution,[],[f622,f69])).
% 1.45/0.56  fof(f69,plain,(
% 1.45/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.45/0.56  fof(f622,plain,(
% 1.45/0.56    ~v1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.45/0.56    inference(forward_demodulation,[],[f621,f586])).
% 1.45/0.56  fof(f621,plain,(
% 1.45/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f620])).
% 1.45/0.56  fof(f620,plain,(
% 1.45/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f619,f98])).
% 1.45/0.56  fof(f98,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.56    inference(superposition,[],[f83,f95])).
% 1.45/0.56  fof(f619,plain,(
% 1.45/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(forward_demodulation,[],[f590,f586])).
% 1.45/0.56  fof(f590,plain,(
% 1.45/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f232,f586])).
% 1.45/0.56  fof(f232,plain,(
% 1.45/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(superposition,[],[f75,f230])).
% 1.45/0.56  fof(f230,plain,(
% 1.45/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(resolution,[],[f223,f53])).
% 1.45/0.56  fof(f223,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))) )),
% 1.45/0.56    inference(resolution,[],[f221,f63])).
% 1.45/0.56  fof(f221,plain,(
% 1.45/0.56    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.45/0.56    inference(resolution,[],[f219,f50])).
% 1.45/0.56  % (10485)Refutation not found, incomplete strategy% (10485)------------------------------
% 1.45/0.56  % (10485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  fof(f219,plain,(
% 1.45/0.56    ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f193,f52])).
% 1.45/0.56  % (10485)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10485)Memory used [KB]: 1791
% 1.45/0.56  % (10485)Time elapsed: 0.162 s
% 1.45/0.56  % (10485)------------------------------
% 1.45/0.56  % (10485)------------------------------
% 1.45/0.56  fof(f193,plain,(
% 1.45/0.56    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.45/0.56    inference(resolution,[],[f112,f53])).
% 1.45/0.56  fof(f112,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v3_funct_2(X0,X1,X2) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f109])).
% 1.45/0.56  fof(f109,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(resolution,[],[f65,f68])).
% 1.45/0.56  fof(f68,plain,(
% 1.45/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f32])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f31])).
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.45/0.56  fof(f688,plain,(
% 1.45/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 1.45/0.56    inference(backward_demodulation,[],[f598,f666])).
% 1.45/0.56  fof(f666,plain,(
% 1.45/0.56    k1_xboole_0 = sK1),
% 1.45/0.56    inference(resolution,[],[f529,f401])).
% 1.45/0.56  fof(f401,plain,(
% 1.45/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.45/0.56    inference(backward_demodulation,[],[f49,f398])).
% 1.45/0.56  fof(f529,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1) )),
% 1.45/0.56    inference(resolution,[],[f452,f63])).
% 1.45/0.56  fof(f452,plain,(
% 1.45/0.56    ~v1_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f426])).
% 1.45/0.56  fof(f426,plain,(
% 1.45/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 1.45/0.56    inference(backward_demodulation,[],[f260,f398])).
% 1.45/0.56  fof(f260,plain,(
% 1.45/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 1.45/0.56    inference(superposition,[],[f75,f249])).
% 1.45/0.56  fof(f598,plain,(
% 1.45/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1))),
% 1.45/0.56    inference(backward_demodulation,[],[f418,f586])).
% 1.45/0.56  fof(f418,plain,(
% 1.45/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 1.45/0.56    inference(backward_demodulation,[],[f160,f398])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (10473)------------------------------
% 1.45/0.56  % (10473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10473)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (10473)Memory used [KB]: 2046
% 1.45/0.56  % (10473)Time elapsed: 0.152 s
% 1.45/0.56  % (10473)------------------------------
% 1.45/0.56  % (10473)------------------------------
% 1.45/0.56  % (10464)Success in time 0.199 s
%------------------------------------------------------------------------------
