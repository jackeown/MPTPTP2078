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
% DateTime   : Thu Dec  3 13:00:39 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  130 (2084 expanded)
%              Number of leaves         :   18 ( 452 expanded)
%              Depth                    :   29
%              Number of atoms          :  311 (8614 expanded)
%              Number of equality atoms :  123 (2133 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23419)Termination reason: Refutation not found, incomplete strategy

% (23419)Memory used [KB]: 10746
% (23419)Time elapsed: 0.160 s
% (23419)------------------------------
% (23419)------------------------------
fof(f1318,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1169,f666])).

fof(f666,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f664,f446])).

fof(f446,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f444,f138])).

fof(f138,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f45,f126])).

fof(f126,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f121,f115])).

fof(f115,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f444,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f401,f131])).

fof(f131,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f91,f126])).

fof(f91,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f44,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f401,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f67,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

% (23433)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f664,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f86,f131])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f80,f78])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f1169,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f1108,f1113])).

fof(f1113,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f1112,f78])).

fof(f1112,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1111,f1065])).

fof(f1065,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1064,f38])).

fof(f38,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f1064,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f966,f526])).

fof(f526,plain,(
    ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f520,f138])).

fof(f520,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f399,f109])).

fof(f109,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f108,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

% (23410)Refutation not found, incomplete strategy% (23410)------------------------------
% (23410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23410)Termination reason: Refutation not found, incomplete strategy

% (23410)Memory used [KB]: 10874
% (23410)Time elapsed: 0.156 s
% (23410)------------------------------
% (23410)------------------------------
fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f399,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
      | k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    inference(resolution,[],[f67,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f966,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f961])).

fof(f961,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f843,f890])).

fof(f890,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f889,f77])).

fof(f889,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f888,f109])).

fof(f888,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f875,f77])).

fof(f875,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f702,f863])).

fof(f863,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f855])).

fof(f855,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f743,f844])).

fof(f844,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f843,f397])).

fof(f397,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f743,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f84,f691,f742])).

fof(f742,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(forward_demodulation,[],[f734,f693])).

fof(f693,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f691,f67])).

fof(f734,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f73,f691])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f691,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f675,f192])).

fof(f192,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(resolution,[],[f187,f168])).

fof(f168,plain,(
    ! [X6] :
      ( ~ v4_relat_1(sK3,X6)
      | r1_tarski(k1_relat_1(sK3),X6) ) ),
    inference(resolution,[],[f53,f114])).

fof(f114,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f99,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f187,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f675,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(subsumption_resolution,[],[f671,f114])).

fof(f671,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(resolution,[],[f65,f338])).

fof(f338,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f42,f332])).

fof(f332,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f66,f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f84,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f37,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f702,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK2) ),
    inference(resolution,[],[f697,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f697,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f691,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f843,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f839,f41])).

fof(f839,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1111,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1110,f109])).

fof(f1110,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1070,f78])).

fof(f1070,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f183,f1065])).

fof(f183,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f56,f93])).

fof(f93,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f61,f41])).

% (23435)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f1108,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f1107,f1105])).

fof(f1105,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1067,f78])).

fof(f1067,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f41,f1065])).

fof(f1107,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f1106,f78])).

fof(f1106,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f1068,f1065])).

fof(f1068,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f84,f1065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23411)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (23420)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (23413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (23436)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.52  % (23431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (23418)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.53  % (23424)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.53  % (23430)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (23415)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (23434)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.53  % (23414)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (23422)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (23421)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (23438)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (23408)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (23423)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (23410)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (23431)Refutation not found, incomplete strategy% (23431)------------------------------
% 1.36/0.55  % (23431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (23432)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (23431)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (23431)Memory used [KB]: 11001
% 1.36/0.55  % (23431)Time elapsed: 0.077 s
% 1.36/0.55  % (23431)------------------------------
% 1.36/0.55  % (23431)------------------------------
% 1.36/0.55  % (23437)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (23425)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.56  % (23426)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.56  % (23409)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.56  % (23416)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.56  % (23427)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (23429)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.57  % (23428)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.57  % (23417)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.57  % (23419)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.57  % (23415)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % (23419)Refutation not found, incomplete strategy% (23419)------------------------------
% 1.36/0.57  % (23419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  % (23419)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (23419)Memory used [KB]: 10746
% 1.36/0.57  % (23419)Time elapsed: 0.160 s
% 1.36/0.57  % (23419)------------------------------
% 1.36/0.57  % (23419)------------------------------
% 1.36/0.57  fof(f1318,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(subsumption_resolution,[],[f1169,f666])).
% 1.36/0.57  fof(f666,plain,(
% 1.36/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f664,f446])).
% 1.36/0.57  fof(f446,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f444,f138])).
% 1.36/0.57  fof(f138,plain,(
% 1.36/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.57    inference(superposition,[],[f45,f126])).
% 1.36/0.57  fof(f126,plain,(
% 1.36/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.36/0.57    inference(equality_resolution,[],[f122])).
% 1.36/0.57  fof(f122,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f121,f115])).
% 1.36/0.57  fof(f115,plain,(
% 1.36/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.57    inference(resolution,[],[f99,f44])).
% 1.36/0.57  fof(f44,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f16])).
% 1.36/0.57  fof(f16,axiom,(
% 1.36/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.36/0.57  fof(f99,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.36/0.57    inference(resolution,[],[f49,f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f9])).
% 1.36/0.57  fof(f9,axiom,(
% 1.36/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.57  fof(f49,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f26])).
% 1.36/0.57  fof(f26,plain,(
% 1.36/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f7])).
% 1.36/0.57  fof(f7,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.57  fof(f121,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 != X0 | ~v1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) )),
% 1.36/0.57    inference(superposition,[],[f47,f45])).
% 1.36/0.57  fof(f47,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f25])).
% 1.36/0.57  fof(f25,plain,(
% 1.36/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f10])).
% 1.36/0.57  fof(f10,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.57  fof(f45,plain,(
% 1.36/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f11])).
% 1.36/0.57  fof(f11,axiom,(
% 1.36/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.57  fof(f444,plain,(
% 1.36/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.36/0.57    inference(resolution,[],[f401,f131])).
% 1.36/0.57  fof(f131,plain,(
% 1.36/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.36/0.57    inference(backward_demodulation,[],[f91,f126])).
% 1.36/0.57  fof(f91,plain,(
% 1.36/0.57    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.36/0.57    inference(superposition,[],[f44,f77])).
% 1.36/0.57  fof(f77,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.36/0.57    inference(equality_resolution,[],[f64])).
% 1.36/0.57  fof(f64,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f5])).
% 1.36/0.57  fof(f5,axiom,(
% 1.36/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.36/0.57  fof(f401,plain,(
% 1.36/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 1.36/0.57    inference(superposition,[],[f67,f78])).
% 1.36/0.57  fof(f78,plain,(
% 1.36/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f63])).
% 1.36/0.57  fof(f63,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f5])).
% 1.36/0.57  fof(f67,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f33])).
% 1.36/0.57  fof(f33,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(ennf_transformation,[],[f13])).
% 1.36/0.57  % (23433)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.57  fof(f664,plain,(
% 1.36/0.57    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.36/0.57    inference(resolution,[],[f86,f131])).
% 1.36/0.57  fof(f86,plain,(
% 1.36/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f80,f78])).
% 1.36/0.57  fof(f80,plain,(
% 1.36/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f71])).
% 1.36/0.57  fof(f71,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f36])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(flattening,[],[f35])).
% 1.36/0.57  fof(f35,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.57    inference(ennf_transformation,[],[f17])).
% 1.36/0.57  fof(f17,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.57  fof(f1169,plain,(
% 1.36/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 1.36/0.57    inference(backward_demodulation,[],[f1108,f1113])).
% 1.36/0.57  fof(f1113,plain,(
% 1.36/0.57    k1_xboole_0 = sK3),
% 1.36/0.57    inference(forward_demodulation,[],[f1112,f78])).
% 1.36/0.57  fof(f1112,plain,(
% 1.36/0.57    sK3 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.36/0.57    inference(forward_demodulation,[],[f1111,f1065])).
% 1.36/0.57  fof(f1065,plain,(
% 1.36/0.57    k1_xboole_0 = sK0),
% 1.36/0.57    inference(subsumption_resolution,[],[f1064,f38])).
% 1.36/0.57  fof(f38,plain,(
% 1.36/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.36/0.57    inference(cnf_transformation,[],[f23])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.36/0.57    inference(flattening,[],[f22])).
% 1.36/0.57  fof(f22,plain,(
% 1.36/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.36/0.57    inference(ennf_transformation,[],[f19])).
% 1.36/0.57  fof(f19,negated_conjecture,(
% 1.36/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.36/0.57    inference(negated_conjecture,[],[f18])).
% 1.36/0.57  fof(f18,conjecture,(
% 1.36/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.36/0.57  fof(f1064,plain,(
% 1.36/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.36/0.57    inference(forward_demodulation,[],[f966,f526])).
% 1.36/0.57  fof(f526,plain,(
% 1.36/0.57    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f520,f138])).
% 1.36/0.57  fof(f520,plain,(
% 1.36/0.57    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 1.36/0.57    inference(resolution,[],[f399,f109])).
% 1.36/0.57  fof(f109,plain,(
% 1.36/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.57    inference(resolution,[],[f108,f43])).
% 1.36/0.57  fof(f43,plain,(
% 1.36/0.57    v1_xboole_0(k1_xboole_0)),
% 1.36/0.57    inference(cnf_transformation,[],[f3])).
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    v1_xboole_0(k1_xboole_0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.36/0.57  fof(f108,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(resolution,[],[f58,f50])).
% 1.36/0.57  fof(f50,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f27])).
% 1.36/0.57  fof(f27,plain,(
% 1.36/0.57    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f20])).
% 1.36/0.57  fof(f20,plain,(
% 1.36/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.36/0.57  fof(f1,axiom,(
% 1.36/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.58  % (23410)Refutation not found, incomplete strategy% (23410)------------------------------
% 1.36/0.58  % (23410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (23410)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (23410)Memory used [KB]: 10874
% 1.36/0.58  % (23410)Time elapsed: 0.156 s
% 1.36/0.58  % (23410)------------------------------
% 1.36/0.58  % (23410)------------------------------
% 1.36/0.58  fof(f58,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f29])).
% 1.36/0.58  fof(f29,plain,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f2])).
% 1.36/0.58  fof(f2,axiom,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.58  fof(f399,plain,(
% 1.36/0.58    ( ! [X2,X3,X1] : (~r1_tarski(X3,k2_zfmisc_1(X1,X2)) | k1_relset_1(X1,X2,X3) = k1_relat_1(X3)) )),
% 1.36/0.58    inference(resolution,[],[f67,f60])).
% 1.36/0.58  fof(f60,plain,(
% 1.36/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f6])).
% 1.36/0.58  fof(f6,axiom,(
% 1.36/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.36/0.58  fof(f966,plain,(
% 1.36/0.58    sK0 = k1_relset_1(sK0,sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(duplicate_literal_removal,[],[f961])).
% 1.36/0.58  fof(f961,plain,(
% 1.36/0.58    sK0 = k1_relset_1(sK0,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.36/0.58    inference(superposition,[],[f843,f890])).
% 1.36/0.58  fof(f890,plain,(
% 1.36/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK1),
% 1.36/0.58    inference(forward_demodulation,[],[f889,f77])).
% 1.36/0.58  fof(f889,plain,(
% 1.36/0.58    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(subsumption_resolution,[],[f888,f109])).
% 1.36/0.58  fof(f888,plain,(
% 1.36/0.58    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(forward_demodulation,[],[f875,f77])).
% 1.36/0.58  fof(f875,plain,(
% 1.36/0.58    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(superposition,[],[f702,f863])).
% 1.36/0.58  fof(f863,plain,(
% 1.36/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.36/0.58    inference(trivial_inequality_removal,[],[f855])).
% 1.36/0.58  fof(f855,plain,(
% 1.36/0.58    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.36/0.58    inference(superposition,[],[f743,f844])).
% 1.36/0.58  fof(f844,plain,(
% 1.36/0.58    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(superposition,[],[f843,f397])).
% 1.36/0.58  fof(f397,plain,(
% 1.36/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.36/0.58    inference(resolution,[],[f67,f41])).
% 1.36/0.58  fof(f41,plain,(
% 1.36/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.58    inference(cnf_transformation,[],[f23])).
% 1.36/0.58  fof(f743,plain,(
% 1.36/0.58    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.36/0.58    inference(global_subsumption,[],[f84,f691,f742])).
% 1.36/0.58  fof(f742,plain,(
% 1.36/0.58    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 1.36/0.58    inference(forward_demodulation,[],[f734,f693])).
% 1.36/0.58  fof(f693,plain,(
% 1.36/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.36/0.58    inference(resolution,[],[f691,f67])).
% 1.36/0.58  fof(f734,plain,(
% 1.36/0.58    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2)),
% 1.36/0.58    inference(resolution,[],[f73,f691])).
% 1.36/0.58  fof(f73,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f36])).
% 1.36/0.58  fof(f691,plain,(
% 1.36/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.36/0.58    inference(resolution,[],[f675,f192])).
% 1.36/0.58  fof(f192,plain,(
% 1.36/0.58    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.36/0.58    inference(resolution,[],[f187,f168])).
% 1.36/0.58  fof(f168,plain,(
% 1.36/0.58    ( ! [X6] : (~v4_relat_1(sK3,X6) | r1_tarski(k1_relat_1(sK3),X6)) )),
% 1.36/0.58    inference(resolution,[],[f53,f114])).
% 1.36/0.58  fof(f114,plain,(
% 1.36/0.58    v1_relat_1(sK3)),
% 1.36/0.58    inference(resolution,[],[f99,f41])).
% 1.36/0.58  fof(f53,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f28])).
% 1.36/0.58  fof(f28,plain,(
% 1.36/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.58    inference(ennf_transformation,[],[f8])).
% 1.36/0.58  fof(f8,axiom,(
% 1.36/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.36/0.58  fof(f187,plain,(
% 1.36/0.58    v4_relat_1(sK3,sK0)),
% 1.36/0.58    inference(resolution,[],[f68,f41])).
% 1.36/0.58  fof(f68,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f34])).
% 1.36/0.58  fof(f34,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f21])).
% 1.36/0.58  fof(f21,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.36/0.58    inference(pure_predicate_removal,[],[f12])).
% 1.36/0.58  fof(f12,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.58  fof(f675,plain,(
% 1.36/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.36/0.58    inference(subsumption_resolution,[],[f671,f114])).
% 1.36/0.58  fof(f671,plain,(
% 1.36/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.36/0.58    inference(resolution,[],[f65,f338])).
% 1.36/0.58  fof(f338,plain,(
% 1.36/0.58    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.36/0.58    inference(backward_demodulation,[],[f42,f332])).
% 1.36/0.58  fof(f332,plain,(
% 1.36/0.58    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.36/0.58    inference(resolution,[],[f66,f41])).
% 1.36/0.58  fof(f66,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f32])).
% 1.36/0.58  fof(f32,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f14])).
% 1.36/0.58  fof(f14,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.58  fof(f42,plain,(
% 1.36/0.58    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.36/0.58    inference(cnf_transformation,[],[f23])).
% 1.36/0.58  fof(f65,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f31])).
% 1.36/0.58  fof(f31,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.36/0.58    inference(flattening,[],[f30])).
% 1.36/0.58  fof(f30,plain,(
% 1.36/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.36/0.58    inference(ennf_transformation,[],[f15])).
% 1.36/0.58  fof(f15,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.36/0.58  fof(f84,plain,(
% 1.36/0.58    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.36/0.58    inference(subsumption_resolution,[],[f37,f39])).
% 1.36/0.58  fof(f39,plain,(
% 1.36/0.58    v1_funct_1(sK3)),
% 1.36/0.58    inference(cnf_transformation,[],[f23])).
% 1.36/0.58  fof(f37,plain,(
% 1.36/0.58    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.36/0.58    inference(cnf_transformation,[],[f23])).
% 1.36/0.58  fof(f702,plain,(
% 1.36/0.58    ~r1_tarski(k2_zfmisc_1(sK0,sK2),sK3) | sK3 = k2_zfmisc_1(sK0,sK2)),
% 1.36/0.58    inference(resolution,[],[f697,f56])).
% 1.36/0.58  fof(f56,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.36/0.58    inference(cnf_transformation,[],[f4])).
% 1.36/0.58  fof(f4,axiom,(
% 1.36/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.58  fof(f697,plain,(
% 1.36/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.36/0.58    inference(resolution,[],[f691,f61])).
% 1.36/0.58  fof(f61,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f6])).
% 1.36/0.58  fof(f843,plain,(
% 1.36/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.36/0.58    inference(subsumption_resolution,[],[f839,f41])).
% 1.36/0.58  fof(f839,plain,(
% 1.36/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.58    inference(resolution,[],[f74,f40])).
% 1.36/0.58  fof(f40,plain,(
% 1.36/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.36/0.58    inference(cnf_transformation,[],[f23])).
% 1.36/0.58  fof(f74,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f36])).
% 1.36/0.58  fof(f1111,plain,(
% 1.36/0.58    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.58    inference(subsumption_resolution,[],[f1110,f109])).
% 1.36/0.58  fof(f1110,plain,(
% 1.36/0.58    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.58    inference(forward_demodulation,[],[f1070,f78])).
% 1.36/0.58  fof(f1070,plain,(
% 1.36/0.58    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.58    inference(backward_demodulation,[],[f183,f1065])).
% 1.36/0.58  fof(f183,plain,(
% 1.36/0.58    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.58    inference(resolution,[],[f56,f93])).
% 1.36/0.58  fof(f93,plain,(
% 1.36/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.36/0.58    inference(resolution,[],[f61,f41])).
% 1.36/0.58  % (23435)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.58  fof(f1108,plain,(
% 1.36/0.58    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.36/0.58    inference(subsumption_resolution,[],[f1107,f1105])).
% 1.36/0.58  fof(f1105,plain,(
% 1.36/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.36/0.58    inference(forward_demodulation,[],[f1067,f78])).
% 1.36/0.58  fof(f1067,plain,(
% 1.36/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.36/0.58    inference(backward_demodulation,[],[f41,f1065])).
% 1.36/0.58  fof(f1107,plain,(
% 1.36/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.36/0.58    inference(forward_demodulation,[],[f1106,f78])).
% 1.36/0.58  fof(f1106,plain,(
% 1.36/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.36/0.58    inference(forward_demodulation,[],[f1068,f1065])).
% 1.36/0.58  fof(f1068,plain,(
% 1.36/0.58    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.36/0.58    inference(backward_demodulation,[],[f84,f1065])).
% 1.36/0.58  % SZS output end Proof for theBenchmark
% 1.36/0.58  % (23415)------------------------------
% 1.36/0.58  % (23415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (23415)Termination reason: Refutation
% 1.36/0.58  
% 1.36/0.58  % (23415)Memory used [KB]: 6780
% 1.36/0.58  % (23415)Time elapsed: 0.100 s
% 1.36/0.58  % (23415)------------------------------
% 1.36/0.58  % (23415)------------------------------
% 1.36/0.58  % (23404)Success in time 0.213 s
%------------------------------------------------------------------------------
