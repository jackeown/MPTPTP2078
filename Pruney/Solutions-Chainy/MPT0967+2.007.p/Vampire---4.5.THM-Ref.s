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
% DateTime   : Thu Dec  3 13:00:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 (2784 expanded)
%              Number of leaves         :   12 ( 652 expanded)
%              Depth                    :   34
%              Number of atoms          :  395 (16254 expanded)
%              Number of equality atoms :  117 (3592 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f790,plain,(
    $false ),
    inference(subsumption_resolution,[],[f789,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f789,plain,(
    ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f788,f327])).

fof(f327,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(superposition,[],[f34,f322])).

fof(f322,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f302,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f302,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f297,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f297,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f296,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v5_relat_1(sK3,X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f105,f36])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | v5_relat_1(sK3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X0)
      | v5_relat_1(sK3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f66])).

fof(f66,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X0)
      | v5_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f103,plain,(
    ! [X0] :
      ( v5_relat_1(sK3,X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f296,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f293,f78])).

fof(f78,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f293,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK3,sK2)
    | ~ v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f281,f68])).

fof(f68,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(sK3),X1)
      | ~ v4_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f281,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f244,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3),X0)
      | ~ v5_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f42,f66])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f244,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f241,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | v5_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f43,f66])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f241,plain,
    ( k1_xboole_0 = sK2
    | ~ v5_relat_1(sK3,sK2)
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(resolution,[],[f185,f115])).

fof(f115,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f106,f33])).

fof(f106,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(k1_relat_1(sK3),X1)
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f48,f66])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f185,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,sK0,X0)
      | k1_xboole_0 = X0
      | ~ v5_relat_1(sK3,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f176,f98])).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f96,f81])).

fof(f81,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f95,f34])).

fof(f95,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f176,plain,(
    ! [X2] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X2)
      | k1_xboole_0 = X2
      | ~ v5_relat_1(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f174,f163])).

fof(f163,plain,(
    ! [X2] :
      ( ~ v5_relat_1(sK3,X2)
      | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X2,sK3) ) ),
    inference(resolution,[],[f141,f59])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | k1_relat_1(sK3) = k1_relset_1(X0,X1,sK3)
      | ~ v5_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f109,f69])).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_relat_1(sK3),X5)
      | ~ r1_tarski(k1_relat_1(sK3),X4)
      | k1_relat_1(sK3) = k1_relset_1(X4,X5,sK3) ) ),
    inference(resolution,[],[f84,f50])).

fof(f174,plain,(
    ! [X2] :
      ( k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X2,sK3)
      | k1_xboole_0 = X2
      | v1_funct_2(sK3,k1_relat_1(sK3),X2)
      | ~ v5_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f151,f59])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | k1_relset_1(X0,X1,sK3) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(sK3,X0,X1)
      | ~ v5_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f107,f69])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | k1_relset_1(X0,X1,sK3) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(sK3,X0,X1) ) ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f788,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f767,f328])).

fof(f328,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f35,f322])).

fof(f767,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f38,f757])).

fof(f757,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f756,f39])).

fof(f756,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f754,f427])).

fof(f427,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f395,f87])).

fof(f87,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f68,f75])).

fof(f395,plain,(
    v4_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[],[f78,f349])).

fof(f349,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f322])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f754,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f417,f556])).

fof(f556,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f362,f427])).

fof(f362,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f361,f39])).

fof(f361,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f360,f322])).

fof(f360,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f357,f354])).

fof(f354,plain,(
    ! [X0] : k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3) ),
    inference(subsumption_resolution,[],[f340,f39])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3) ) ),
    inference(superposition,[],[f180,f322])).

fof(f180,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X1,sK3) ) ),
    inference(resolution,[],[f163,f103])).

fof(f357,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
      | k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X0,sK3)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f214,f70])).

fof(f70,plain,(
    v4_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f214,plain,(
    ! [X4,X5] :
      ( ~ v4_relat_1(sK3,X5)
      | v1_funct_2(sK3,X5,X4)
      | k1_relset_1(X5,X4,sK3) != X5
      | k1_xboole_0 = X4
      | ~ r1_tarski(sK1,X4) ) ),
    inference(resolution,[],[f173,f103])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X1)
      | k1_xboole_0 = X1
      | v1_funct_2(sK3,X0,X1)
      | k1_relset_1(X0,X1,sK3) != X0
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f151,f68])).

fof(f417,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f416,f39])).

fof(f416,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f398,f352])).

fof(f352,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f337,f39])).

fof(f337,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(superposition,[],[f116,f322])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f92,f103])).

fof(f92,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f69,f75])).

fof(f398,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(superposition,[],[f115,f349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:39:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (8999)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.48  % (8991)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (8985)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (8984)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (8999)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f790,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f789,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.50  fof(f789,plain,(
% 0.21/0.50    ~v1_funct_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f788,f327])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f34,f322])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f302,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(resolution,[],[f47,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f36,f299])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f297,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~r1_tarski(sK2,sK2)),
% 0.21/0.50    inference(resolution,[],[f296,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (v5_relat_1(sK3,X0) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f105,f36])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | v5_relat_1(sK3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f103,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | v5_relat_1(sK3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f44,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f49,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v5_relat_1(X2,X0) | v5_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0] : (v5_relat_1(sK3,X0) | ~r1_tarski(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f80,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    v5_relat_1(sK3,sK1)),
% 0.21/0.50    inference(resolution,[],[f52,f35])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ~v5_relat_1(sK3,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v4_relat_1(sK3,sK0)),
% 0.21/0.50    inference(resolution,[],[f51,f35])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,sK2) | ~v4_relat_1(sK3,sK0)),
% 0.21/0.50    inference(resolution,[],[f281,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(k1_relat_1(sK3),X1) | ~v4_relat_1(sK3,X1)) )),
% 0.21/0.50    inference(resolution,[],[f66,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~v5_relat_1(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f244,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK3),X0) | ~v5_relat_1(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f42,f66])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f241,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v5_relat_1(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f66])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~v5_relat_1(sK3,sK2) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.50    inference(resolution,[],[f185,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK2) | ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f106,f33])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),sK0) | ~r1_tarski(k2_relat_1(sK3),sK2) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f84,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK3),X1) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 0.21/0.50    inference(resolution,[],[f48,f66])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | k1_xboole_0 = X0 | ~v5_relat_1(sK3,X0) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(superposition,[],[f176,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f96,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(resolution,[],[f50,f35])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f34])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(resolution,[],[f53,f35])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X2] : (v1_funct_2(sK3,k1_relat_1(sK3),X2) | k1_xboole_0 = X2 | ~v5_relat_1(sK3,X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f174,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2] : (~v5_relat_1(sK3,X2) | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X2,sK3)) )),
% 0.21/0.50    inference(resolution,[],[f141,f59])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X0) | k1_relat_1(sK3) = k1_relset_1(X0,X1,sK3) | ~v5_relat_1(sK3,X1)) )),
% 0.21/0.50    inference(resolution,[],[f109,f69])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~r1_tarski(k2_relat_1(sK3),X5) | ~r1_tarski(k1_relat_1(sK3),X4) | k1_relat_1(sK3) = k1_relset_1(X4,X5,sK3)) )),
% 0.21/0.50    inference(resolution,[],[f84,f50])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X2] : (k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X2,sK3) | k1_xboole_0 = X2 | v1_funct_2(sK3,k1_relat_1(sK3),X2) | ~v5_relat_1(sK3,X2)) )),
% 0.21/0.50    inference(resolution,[],[f151,f59])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X0) | k1_relset_1(X0,X1,sK3) != X0 | k1_xboole_0 = X1 | v1_funct_2(sK3,X0,X1) | ~v5_relat_1(sK3,X1)) )),
% 0.21/0.50    inference(resolution,[],[f107,f69])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X1) | ~r1_tarski(k1_relat_1(sK3),X0) | k1_relset_1(X0,X1,sK3) != X0 | k1_xboole_0 = X1 | v1_funct_2(sK3,X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f84,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f788,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f767,f328])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(superposition,[],[f35,f322])).
% 0.21/0.50  fof(f767,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(superposition,[],[f38,f757])).
% 0.21/0.50  fof(f757,plain,(
% 0.21/0.50    k1_xboole_0 = sK2),
% 0.21/0.50    inference(subsumption_resolution,[],[f756,f39])).
% 0.21/0.50  fof(f756,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.50    inference(forward_demodulation,[],[f754,f427])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f395,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f68,f75])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    v4_relat_1(sK3,k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f78,f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    k1_xboole_0 = sK0),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f330])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f37,f322])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f754,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.50    inference(resolution,[],[f417,f556])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK3,k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(superposition,[],[f362,f427])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK3,k1_relat_1(sK3),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f361,f39])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK3,k1_relat_1(sK3),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f360,f322])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK3,k1_relat_1(sK3),X0) | k1_xboole_0 = X0 | ~r1_tarski(sK1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f357,f354])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f340,f39])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X0,sK3)) )),
% 0.21/0.50    inference(superposition,[],[f180,f322])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK1,X1) | k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),X1,sK3)) )),
% 0.21/0.50    inference(resolution,[],[f163,f103])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK3,k1_relat_1(sK3),X0) | k1_relat_1(sK3) != k1_relset_1(k1_relat_1(sK3),X0,sK3) | k1_xboole_0 = X0 | ~r1_tarski(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f214,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    v4_relat_1(sK3,k1_relat_1(sK3))),
% 0.21/0.50    inference(resolution,[],[f67,f59])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | v4_relat_1(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f66,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~v4_relat_1(sK3,X5) | v1_funct_2(sK3,X5,X4) | k1_relset_1(X5,X4,sK3) != X5 | k1_xboole_0 = X4 | ~r1_tarski(sK1,X4)) )),
% 0.21/0.50    inference(resolution,[],[f173,f103])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X1) | k1_xboole_0 = X1 | v1_funct_2(sK3,X0,X1) | k1_relset_1(X0,X1,sK3) != X0 | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f151,f68])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f416,f39])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,sK2) | ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.50    inference(forward_demodulation,[],[f398,f352])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f337,f39])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.50    inference(superposition,[],[f116,f322])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f92,f103])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~v5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f69,f75])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f115,f349])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8999)------------------------------
% 0.21/0.50  % (8999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8999)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8999)Memory used [KB]: 1791
% 0.21/0.50  % (8999)Time elapsed: 0.073 s
% 0.21/0.50  % (8999)------------------------------
% 0.21/0.50  % (8999)------------------------------
% 0.21/0.50  % (8982)Success in time 0.141 s
%------------------------------------------------------------------------------
