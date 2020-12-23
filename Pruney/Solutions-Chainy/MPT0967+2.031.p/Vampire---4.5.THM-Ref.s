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
% DateTime   : Thu Dec  3 13:00:47 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  131 (2201 expanded)
%              Number of leaves         :   18 ( 484 expanded)
%              Depth                    :   29
%              Number of atoms          :  319 (9141 expanded)
%              Number of equality atoms :   84 (2038 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1027,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1026,f1022])).

fof(f1022,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f1001,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1001,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f702,f991])).

fof(f991,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f44,f847,f990])).

fof(f990,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f982,f102])).

fof(f102,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f100,f49])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f982,plain,
    ( sK0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f730,f948])).

fof(f948,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f947,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f947,plain,(
    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f946,f847])).

fof(f946,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f945,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f945,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f854,f87])).

fof(f854,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f135,f847])).

fof(f135,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f61,f105])).

fof(f105,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f730,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f94,f315,f729])).

fof(f729,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f726,f315])).

fof(f726,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(superposition,[],[f81,f477])).

fof(f477,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f76,f315])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f315,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f310,f48])).

fof(f48,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f310,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f306,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f306,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f300,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f300,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),X4)
      | m1_subset_1(sK3,X4) ) ),
    inference(resolution,[],[f289,f114])).

fof(f114,plain,(
    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f112,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f43,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f847,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f787,f132])).

fof(f132,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f61,f51])).

fof(f787,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f48,f786])).

fof(f786,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f784])).

fof(f784,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f730,f779])).

fof(f779,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f777,f476])).

fof(f476,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f76,f47])).

fof(f777,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f773,f47])).

fof(f773,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f702,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f686,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f686,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f678,f58])).

fof(f678,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_zfmisc_1(sK2),X0)
      | m1_subset_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f675,f289])).

fof(f675,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f653,f51])).

fof(f653,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4(k1_zfmisc_1(sK1)))
      | r2_hidden(X0,k1_zfmisc_1(sK2)) ) ),
    inference(resolution,[],[f651,f494])).

fof(f494,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f177,f58])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X2),X1)
      | r2_hidden(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f62,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r2_hidden(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f57,f65])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f651,plain,(
    r1_tarski(sK4(k1_zfmisc_1(sK1)),sK2) ),
    inference(resolution,[],[f646,f513])).

fof(f513,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f509,f50])).

fof(f509,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f356,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f356,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_zfmisc_1(X4))
      | v1_xboole_0(X3)
      | r1_tarski(sK4(X3),X4) ) ),
    inference(resolution,[],[f302,f66])).

fof(f302,plain,(
    ! [X8,X7] :
      ( m1_subset_1(sK4(X7),X8)
      | ~ r1_tarski(X7,X8)
      | v1_xboole_0(X7) ) ),
    inference(resolution,[],[f289,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f646,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r1_tarski(X2,sK2) ) ),
    inference(resolution,[],[f643,f66])).

fof(f643,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(sK2))
      | ~ r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f624,f85])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(sK2),X1)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f618,f289])).

fof(f618,plain,(
    ! [X18] :
      ( r2_hidden(X18,k1_zfmisc_1(sK2))
      | ~ r1_tarski(X18,sK1) ) ),
    inference(resolution,[],[f494,f48])).

fof(f1026,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1020,f146])).

fof(f146,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(superposition,[],[f73,f137])).

fof(f137,plain,(
    ! [X6] : k1_xboole_0 = sK6(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f136,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_xboole_0,sK6(X6,k1_xboole_0))
      | k1_xboole_0 = sK6(X6,k1_xboole_0) ) ),
    inference(resolution,[],[f61,f127])).

fof(f127,plain,(
    ! [X0] : r1_tarski(sK6(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f124,f66])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(sK6(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f71,f87])).

fof(f71,plain,(
    ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f73,plain,(
    ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f25])).

fof(f1020,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f987,f991])).

fof(f987,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(k1_xboole_0,sK0,sK2) ),
    inference(forward_demodulation,[],[f950,f948])).

fof(f950,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f94,f948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:12:42 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (3295)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3292)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3291)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (3304)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.18/0.52  % (3303)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.53  % (3299)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.53  % (3296)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.53  % (3313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.53  % (3294)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.18/0.53  % (3315)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.18/0.53  % (3307)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.18/0.53  % (3305)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.18/0.53  % (3298)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.18/0.53  % (3320)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.18/0.54  % (3302)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.54  % (3297)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.18/0.54  % (3314)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.18/0.54  % (3311)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (3317)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.54  % (3306)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (3293)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.54  % (3318)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (3301)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (3293)Refutation not found, incomplete strategy% (3293)------------------------------
% 1.41/0.55  % (3293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3293)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3293)Memory used [KB]: 10746
% 1.41/0.55  % (3293)Time elapsed: 0.136 s
% 1.41/0.55  % (3293)------------------------------
% 1.41/0.55  % (3293)------------------------------
% 1.41/0.55  % (3312)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (3313)Refutation not found, incomplete strategy% (3313)------------------------------
% 1.41/0.55  % (3313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3313)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3313)Memory used [KB]: 10874
% 1.41/0.55  % (3313)Time elapsed: 0.087 s
% 1.41/0.55  % (3313)------------------------------
% 1.41/0.55  % (3313)------------------------------
% 1.41/0.55  % (3299)Refutation not found, incomplete strategy% (3299)------------------------------
% 1.41/0.55  % (3299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3299)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3299)Memory used [KB]: 10746
% 1.41/0.55  % (3299)Time elapsed: 0.131 s
% 1.41/0.55  % (3299)------------------------------
% 1.41/0.55  % (3299)------------------------------
% 1.41/0.55  % (3308)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (3300)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (3309)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (3310)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (3319)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (3316)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.60  % (3297)Refutation found. Thanks to Tanya!
% 1.41/0.60  % SZS status Theorem for theBenchmark
% 1.41/0.60  % SZS output start Proof for theBenchmark
% 1.41/0.60  fof(f1027,plain,(
% 1.41/0.60    $false),
% 1.41/0.60    inference(subsumption_resolution,[],[f1026,f1022])).
% 1.41/0.60  fof(f1022,plain,(
% 1.41/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.60    inference(subsumption_resolution,[],[f1001,f49])).
% 1.41/0.60  fof(f49,plain,(
% 1.41/0.60    v1_xboole_0(k1_xboole_0)),
% 1.41/0.60    inference(cnf_transformation,[],[f3])).
% 1.41/0.60  fof(f3,axiom,(
% 1.41/0.60    v1_xboole_0(k1_xboole_0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.60  fof(f1001,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.60    inference(backward_demodulation,[],[f702,f991])).
% 1.41/0.60  fof(f991,plain,(
% 1.41/0.60    k1_xboole_0 = sK2),
% 1.41/0.60    inference(global_subsumption,[],[f44,f847,f990])).
% 1.41/0.60  fof(f990,plain,(
% 1.41/0.60    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 1.41/0.60    inference(forward_demodulation,[],[f982,f102])).
% 1.41/0.60  fof(f102,plain,(
% 1.41/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.60    inference(resolution,[],[f100,f49])).
% 1.41/0.60  fof(f100,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.41/0.60    inference(resolution,[],[f53,f52])).
% 1.41/0.60  fof(f52,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.41/0.60    inference(cnf_transformation,[],[f28])).
% 1.41/0.60  fof(f28,plain,(
% 1.41/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f4])).
% 1.41/0.60  fof(f4,axiom,(
% 1.41/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.41/0.60  fof(f53,plain,(
% 1.41/0.60    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f29])).
% 1.41/0.60  fof(f29,plain,(
% 1.41/0.60    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f16])).
% 1.41/0.60  fof(f16,axiom,(
% 1.41/0.60    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.41/0.60  fof(f982,plain,(
% 1.41/0.60    sK0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2),
% 1.41/0.60    inference(backward_demodulation,[],[f730,f948])).
% 1.41/0.60  fof(f948,plain,(
% 1.41/0.60    k1_xboole_0 = sK3),
% 1.41/0.60    inference(forward_demodulation,[],[f947,f87])).
% 1.41/0.60  fof(f87,plain,(
% 1.41/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.60    inference(equality_resolution,[],[f69])).
% 1.41/0.60  fof(f69,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f8])).
% 1.41/0.60  fof(f8,axiom,(
% 1.41/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.60  fof(f947,plain,(
% 1.41/0.60    sK3 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.41/0.60    inference(forward_demodulation,[],[f946,f847])).
% 1.41/0.60  fof(f946,plain,(
% 1.41/0.60    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.60    inference(subsumption_resolution,[],[f945,f51])).
% 1.41/0.60  fof(f51,plain,(
% 1.41/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f6])).
% 1.41/0.60  fof(f6,axiom,(
% 1.41/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.60  fof(f945,plain,(
% 1.41/0.60    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.60    inference(forward_demodulation,[],[f854,f87])).
% 1.41/0.60  fof(f854,plain,(
% 1.41/0.60    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.60    inference(backward_demodulation,[],[f135,f847])).
% 1.41/0.60  fof(f135,plain,(
% 1.41/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.60    inference(resolution,[],[f61,f105])).
% 1.41/0.60  fof(f105,plain,(
% 1.41/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.41/0.60    inference(resolution,[],[f66,f47])).
% 1.41/0.60  fof(f47,plain,(
% 1.41/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.60    inference(cnf_transformation,[],[f27])).
% 1.41/0.61  fof(f27,plain,(
% 1.41/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.41/0.61    inference(flattening,[],[f26])).
% 1.41/0.61  fof(f26,plain,(
% 1.41/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.41/0.61    inference(ennf_transformation,[],[f22])).
% 1.41/0.61  fof(f22,negated_conjecture,(
% 1.41/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.41/0.61    inference(negated_conjecture,[],[f21])).
% 1.41/0.61  fof(f21,conjecture,(
% 1.41/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.41/0.61  fof(f66,plain,(
% 1.41/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f13])).
% 1.41/0.61  fof(f13,axiom,(
% 1.41/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.61  fof(f61,plain,(
% 1.41/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.41/0.61    inference(cnf_transformation,[],[f5])).
% 1.41/0.61  fof(f5,axiom,(
% 1.41/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.61  fof(f730,plain,(
% 1.41/0.61    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.41/0.61    inference(global_subsumption,[],[f94,f315,f729])).
% 1.41/0.61  fof(f729,plain,(
% 1.41/0.61    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 1.41/0.61    inference(subsumption_resolution,[],[f726,f315])).
% 1.41/0.61  fof(f726,plain,(
% 1.41/0.61    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | v1_funct_2(sK3,sK0,sK2)),
% 1.41/0.61    inference(superposition,[],[f81,f477])).
% 1.41/0.61  fof(f477,plain,(
% 1.41/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.41/0.61    inference(resolution,[],[f76,f315])).
% 1.41/0.61  fof(f76,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f37])).
% 1.41/0.61  fof(f37,plain,(
% 1.41/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.61    inference(ennf_transformation,[],[f18])).
% 1.41/0.61  fof(f18,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.61  fof(f81,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f39])).
% 1.41/0.61  fof(f39,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.61    inference(flattening,[],[f38])).
% 1.41/0.61  fof(f38,plain,(
% 1.41/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.61    inference(ennf_transformation,[],[f19])).
% 1.41/0.61  fof(f19,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.61  fof(f315,plain,(
% 1.41/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.61    inference(resolution,[],[f310,f48])).
% 1.41/0.61  fof(f48,plain,(
% 1.41/0.61    r1_tarski(sK1,sK2)),
% 1.41/0.61    inference(cnf_transformation,[],[f27])).
% 1.41/0.61  fof(f310,plain,(
% 1.41/0.61    ( ! [X1] : (~r1_tarski(sK1,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.41/0.61    inference(resolution,[],[f306,f75])).
% 1.41/0.61  fof(f75,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f36])).
% 1.41/0.61  fof(f36,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.41/0.61    inference(ennf_transformation,[],[f9])).
% 1.41/0.61  fof(f9,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.41/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.41/0.61  fof(f306,plain,(
% 1.41/0.61    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),X0) | m1_subset_1(sK3,k1_zfmisc_1(X0))) )),
% 1.41/0.61    inference(resolution,[],[f300,f58])).
% 1.41/0.61  fof(f58,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f33])).
% 1.41/0.61  fof(f33,plain,(
% 1.41/0.61    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.41/0.61    inference(ennf_transformation,[],[f10])).
% 1.41/0.63  fof(f10,axiom,(
% 1.41/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.41/0.63  fof(f300,plain,(
% 1.41/0.63    ( ! [X4] : (~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),X4) | m1_subset_1(sK3,X4)) )),
% 1.41/0.63    inference(resolution,[],[f289,f114])).
% 1.41/0.63  fof(f114,plain,(
% 1.41/0.63    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.63    inference(subsumption_resolution,[],[f112,f50])).
% 1.41/0.63  fof(f50,plain,(
% 1.41/0.63    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.41/0.63    inference(cnf_transformation,[],[f11])).
% 1.41/0.63  fof(f11,axiom,(
% 1.41/0.63    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.41/0.63  fof(f112,plain,(
% 1.41/0.63    v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.63    inference(resolution,[],[f57,f47])).
% 1.41/0.63  fof(f57,plain,(
% 1.41/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f32])).
% 1.41/0.63  fof(f32,plain,(
% 1.41/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.41/0.63    inference(flattening,[],[f31])).
% 1.41/0.63  fof(f31,plain,(
% 1.41/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.41/0.63    inference(ennf_transformation,[],[f12])).
% 1.41/0.63  fof(f12,axiom,(
% 1.41/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.41/0.63  fof(f289,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X2) | ~r1_tarski(X1,X2)) )),
% 1.41/0.63    inference(resolution,[],[f83,f65])).
% 1.41/0.63  fof(f65,plain,(
% 1.41/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f13])).
% 1.41/0.63  fof(f83,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f41])).
% 1.41/0.63  fof(f41,plain,(
% 1.41/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.41/0.63    inference(flattening,[],[f40])).
% 1.41/0.63  fof(f40,plain,(
% 1.41/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.41/0.63    inference(ennf_transformation,[],[f14])).
% 1.41/0.63  fof(f14,axiom,(
% 1.41/0.63    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.41/0.63  fof(f94,plain,(
% 1.41/0.63    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.63    inference(subsumption_resolution,[],[f43,f45])).
% 1.41/0.63  fof(f45,plain,(
% 1.41/0.63    v1_funct_1(sK3)),
% 1.41/0.63    inference(cnf_transformation,[],[f27])).
% 1.41/0.63  fof(f43,plain,(
% 1.41/0.63    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.63    inference(cnf_transformation,[],[f27])).
% 1.41/0.63  fof(f847,plain,(
% 1.41/0.63    k1_xboole_0 = sK1),
% 1.41/0.63    inference(subsumption_resolution,[],[f787,f132])).
% 1.41/0.63  fof(f132,plain,(
% 1.41/0.63    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.41/0.63    inference(resolution,[],[f61,f51])).
% 1.41/0.63  fof(f787,plain,(
% 1.41/0.63    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.41/0.63    inference(superposition,[],[f48,f786])).
% 1.41/0.63  fof(f786,plain,(
% 1.41/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.63    inference(trivial_inequality_removal,[],[f784])).
% 1.41/0.63  fof(f784,plain,(
% 1.41/0.63    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.63    inference(superposition,[],[f730,f779])).
% 1.41/0.63  fof(f779,plain,(
% 1.41/0.63    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.41/0.63    inference(superposition,[],[f777,f476])).
% 1.41/0.63  fof(f476,plain,(
% 1.41/0.63    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.41/0.63    inference(resolution,[],[f76,f47])).
% 1.41/0.63  fof(f777,plain,(
% 1.41/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.41/0.63    inference(subsumption_resolution,[],[f773,f47])).
% 1.41/0.63  fof(f773,plain,(
% 1.41/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.63    inference(resolution,[],[f82,f46])).
% 1.41/0.63  fof(f46,plain,(
% 1.41/0.63    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.63    inference(cnf_transformation,[],[f27])).
% 1.41/0.63  fof(f82,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.63    inference(cnf_transformation,[],[f39])).
% 1.41/0.63  fof(f44,plain,(
% 1.41/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.41/0.63    inference(cnf_transformation,[],[f27])).
% 1.41/0.63  fof(f702,plain,(
% 1.41/0.63    ( ! [X0] : (~v1_xboole_0(sK2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.63    inference(resolution,[],[f686,f118])).
% 1.41/0.63  fof(f118,plain,(
% 1.41/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.41/0.63    inference(resolution,[],[f63,f55])).
% 1.41/0.63  fof(f55,plain,(
% 1.41/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f1])).
% 1.41/0.63  fof(f1,axiom,(
% 1.41/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.63  fof(f63,plain,(
% 1.41/0.63    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f34])).
% 1.41/0.63  fof(f34,plain,(
% 1.41/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.63    inference(ennf_transformation,[],[f2])).
% 1.41/0.63  fof(f2,axiom,(
% 1.41/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.63  fof(f686,plain,(
% 1.41/0.63    ( ! [X0] : (~r1_tarski(sK2,X0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.63    inference(resolution,[],[f678,f58])).
% 1.41/0.63  fof(f678,plain,(
% 1.41/0.63    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(sK2),X0) | m1_subset_1(k1_xboole_0,X0)) )),
% 1.41/0.63    inference(resolution,[],[f675,f289])).
% 1.41/0.63  fof(f675,plain,(
% 1.41/0.63    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))),
% 1.41/0.63    inference(resolution,[],[f653,f51])).
% 1.41/0.63  fof(f653,plain,(
% 1.41/0.63    ( ! [X0] : (~r1_tarski(X0,sK4(k1_zfmisc_1(sK1))) | r2_hidden(X0,k1_zfmisc_1(sK2))) )),
% 1.41/0.63    inference(resolution,[],[f651,f494])).
% 1.41/0.63  fof(f494,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 1.41/0.63    inference(resolution,[],[f177,f58])).
% 1.41/0.63  fof(f177,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k1_zfmisc_1(X2),X1) | r2_hidden(X0,X1) | ~r1_tarski(X0,X2)) )),
% 1.41/0.63    inference(resolution,[],[f62,f115])).
% 1.41/0.63  fof(f115,plain,(
% 1.41/0.63    ( ! [X0,X1] : (r2_hidden(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.41/0.63    inference(subsumption_resolution,[],[f113,f50])).
% 1.41/0.63  fof(f113,plain,(
% 1.41/0.63    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.41/0.63    inference(resolution,[],[f57,f65])).
% 1.41/0.63  fof(f62,plain,(
% 1.41/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f34])).
% 1.41/0.63  fof(f651,plain,(
% 1.41/0.63    r1_tarski(sK4(k1_zfmisc_1(sK1)),sK2)),
% 1.41/0.63    inference(resolution,[],[f646,f513])).
% 1.41/0.63  fof(f513,plain,(
% 1.41/0.63    ( ! [X0] : (r1_tarski(sK4(k1_zfmisc_1(X0)),X0)) )),
% 1.41/0.63    inference(subsumption_resolution,[],[f509,f50])).
% 1.41/0.63  fof(f509,plain,(
% 1.41/0.63    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(sK4(k1_zfmisc_1(X0)),X0)) )),
% 1.41/0.63    inference(resolution,[],[f356,f85])).
% 1.41/0.63  fof(f85,plain,(
% 1.41/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.63    inference(equality_resolution,[],[f60])).
% 1.41/0.63  fof(f60,plain,(
% 1.41/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.63    inference(cnf_transformation,[],[f5])).
% 1.41/0.63  fof(f356,plain,(
% 1.41/0.63    ( ! [X4,X3] : (~r1_tarski(X3,k1_zfmisc_1(X4)) | v1_xboole_0(X3) | r1_tarski(sK4(X3),X4)) )),
% 1.41/0.63    inference(resolution,[],[f302,f66])).
% 1.41/0.63  fof(f302,plain,(
% 1.41/0.63    ( ! [X8,X7] : (m1_subset_1(sK4(X7),X8) | ~r1_tarski(X7,X8) | v1_xboole_0(X7)) )),
% 1.41/0.63    inference(resolution,[],[f289,f54])).
% 1.41/0.63  fof(f54,plain,(
% 1.41/0.63    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f1])).
% 1.41/0.63  fof(f646,plain,(
% 1.41/0.63    ( ! [X2] : (~r1_tarski(X2,sK1) | r1_tarski(X2,sK2)) )),
% 1.41/0.63    inference(resolution,[],[f643,f66])).
% 1.41/0.63  fof(f643,plain,(
% 1.41/0.63    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(sK2)) | ~r1_tarski(X2,sK1)) )),
% 1.41/0.63    inference(resolution,[],[f624,f85])).
% 1.41/0.63  fof(f624,plain,(
% 1.41/0.63    ( ! [X0,X1] : (~r1_tarski(k1_zfmisc_1(sK2),X1) | m1_subset_1(X0,X1) | ~r1_tarski(X0,sK1)) )),
% 1.41/0.63    inference(resolution,[],[f618,f289])).
% 1.41/0.63  fof(f618,plain,(
% 1.41/0.63    ( ! [X18] : (r2_hidden(X18,k1_zfmisc_1(sK2)) | ~r1_tarski(X18,sK1)) )),
% 1.41/0.63    inference(resolution,[],[f494,f48])).
% 1.41/0.63  fof(f1026,plain,(
% 1.41/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.63    inference(subsumption_resolution,[],[f1020,f146])).
% 1.41/0.63  fof(f146,plain,(
% 1.41/0.63    ( ! [X1] : (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)) )),
% 1.41/0.63    inference(superposition,[],[f73,f137])).
% 1.41/0.63  fof(f137,plain,(
% 1.41/0.63    ( ! [X6] : (k1_xboole_0 = sK6(X6,k1_xboole_0)) )),
% 1.41/0.63    inference(subsumption_resolution,[],[f136,f51])).
% 1.41/0.63  fof(f136,plain,(
% 1.41/0.63    ( ! [X6] : (~r1_tarski(k1_xboole_0,sK6(X6,k1_xboole_0)) | k1_xboole_0 = sK6(X6,k1_xboole_0)) )),
% 1.41/0.63    inference(resolution,[],[f61,f127])).
% 1.41/0.63  fof(f127,plain,(
% 1.41/0.63    ( ! [X0] : (r1_tarski(sK6(X0,k1_xboole_0),k1_xboole_0)) )),
% 1.41/0.63    inference(resolution,[],[f124,f66])).
% 1.41/0.63  fof(f124,plain,(
% 1.41/0.63    ( ! [X0] : (m1_subset_1(sK6(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.41/0.63    inference(superposition,[],[f71,f87])).
% 1.41/0.63  fof(f71,plain,(
% 1.41/0.63    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.63    inference(cnf_transformation,[],[f25])).
% 1.41/0.63  fof(f25,plain,(
% 1.41/0.63    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.63    inference(pure_predicate_removal,[],[f24])).
% 1.41/0.63  fof(f24,plain,(
% 1.41/0.63    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.63    inference(pure_predicate_removal,[],[f23])).
% 1.41/0.63  fof(f23,plain,(
% 1.41/0.63    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.63    inference(pure_predicate_removal,[],[f20])).
% 1.41/0.63  fof(f20,axiom,(
% 1.41/0.63    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.41/0.63  fof(f73,plain,(
% 1.41/0.63    ( ! [X0,X1] : (v1_funct_2(sK6(X0,X1),X0,X1)) )),
% 1.41/0.63    inference(cnf_transformation,[],[f25])).
% 1.41/0.63  fof(f1020,plain,(
% 1.41/0.63    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.63    inference(backward_demodulation,[],[f987,f991])).
% 1.41/0.63  fof(f987,plain,(
% 1.41/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(k1_xboole_0,sK0,sK2)),
% 1.41/0.63    inference(forward_demodulation,[],[f950,f948])).
% 1.41/0.63  fof(f950,plain,(
% 1.41/0.63    ~v1_funct_2(k1_xboole_0,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.63    inference(backward_demodulation,[],[f94,f948])).
% 1.41/0.63  % SZS output end Proof for theBenchmark
% 1.41/0.63  % (3297)------------------------------
% 1.41/0.63  % (3297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.63  % (3297)Termination reason: Refutation
% 1.41/0.63  
% 1.41/0.63  % (3297)Memory used [KB]: 6780
% 1.41/0.63  % (3297)Time elapsed: 0.163 s
% 1.41/0.63  % (3297)------------------------------
% 1.41/0.63  % (3297)------------------------------
% 1.41/0.63  % (3290)Success in time 0.269 s
%------------------------------------------------------------------------------
