%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 (3886 expanded)
%              Number of leaves         :   14 ( 890 expanded)
%              Depth                    :   22
%              Number of atoms          :  282 (11995 expanded)
%              Number of equality atoms :   34 (2375 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f301,f316])).

fof(f316,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f315,f258])).

fof(f258,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f220,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f220,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f121,f211,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | r2_hidden(sK12(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f211,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f210,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f210,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f107,f205,f122,f121,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f122,plain,(
    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f105,f119])).

fof(f119,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f118,f104])).

fof(f104,plain,(
    sK2 = sK9(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sK9(X0,X1,X3) = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sK9(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f33,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f118,plain,(
    sK0 = k1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | k1_relat_1(sK9(X0,X1,X3)) = X0 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK9(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f95,f104])).

fof(f95,plain,(
    v1_funct_2(sK9(sK0,sK1,sK2),k1_relat_1(sK9(sK0,sK1,sK2)),k2_relat_1(sK9(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f93,f94,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f94,plain,(
    v1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( v1_relat_1(sK9(X0,X1,X3))
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK9(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,(
    v1_funct_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( v1_funct_1(sK9(X0,X1,X3))
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK9(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f205,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f107,f202,f203,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f203,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f107,f202,f32])).

fof(f32,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f202,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f199,f119])).

fof(f199,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f106,f115,f70,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f115,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f114,f104])).

fof(f114,plain,(
    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f33,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f94,f104])).

fof(f107,plain,(
    v1_funct_1(sK2) ),
    inference(backward_demodulation,[],[f93,f104])).

fof(f121,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f111,f119])).

fof(f111,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f107,f106,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f315,plain,(
    ! [X1] : v1_funct_2(sK2,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f314,f288])).

fof(f288,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f268,f97])).

fof(f97,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f88,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f34,f37])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f268,plain,(
    sK0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f119,f258])).

fof(f314,plain,(
    ! [X1] : v1_funct_2(sK2,sK0,X1) ),
    inference(subsumption_resolution,[],[f313,f88])).

fof(f313,plain,(
    ! [X1] :
      ( r2_hidden(sK7(k1_xboole_0,X1,k1_xboole_0),k1_xboole_0)
      | v1_funct_2(sK2,sK0,X1) ) ),
    inference(forward_demodulation,[],[f281,f288])).

fof(f281,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK0,X1,k1_xboole_0),sK0)
      | v1_funct_2(sK2,sK0,X1) ) ),
    inference(backward_demodulation,[],[f253,f258])).

fof(f253,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK0,X1,sK2),sK0)
      | v1_funct_2(sK2,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f252,f106])).

fof(f252,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK0,X1,sK2),sK0)
      | ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f250,f107])).

fof(f250,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK0,X1,sK2),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,sK0,X1) ) ),
    inference(superposition,[],[f75,f119])).

fof(f75,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v1_funct_2(X2,k1_relat_1(X2),X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK7(X0,X1,X2),X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f301,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f300,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f300,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f299,f144])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f142,f38])).

fof(f142,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f88,f90,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | r2_hidden(sK11(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f299,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f298,f288])).

fof(f298,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f297,f267])).

fof(f267,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f107,f258])).

fof(f297,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f287,f288])).

fof(f287,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f286,f258])).

fof(f286,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f263,f258])).

fof(f263,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f32,f258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30306)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (30301)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (30301)Refutation not found, incomplete strategy% (30301)------------------------------
% 0.22/0.50  % (30301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30301)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (30301)Memory used [KB]: 10618
% 0.22/0.50  % (30301)Time elapsed: 0.083 s
% 0.22/0.50  % (30301)------------------------------
% 0.22/0.50  % (30301)------------------------------
% 0.22/0.51  % (30299)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (30300)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (30300)Refutation not found, incomplete strategy% (30300)------------------------------
% 0.22/0.51  % (30300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30300)Memory used [KB]: 6140
% 0.22/0.51  % (30300)Time elapsed: 0.095 s
% 0.22/0.51  % (30300)------------------------------
% 0.22/0.51  % (30300)------------------------------
% 0.22/0.51  % (30309)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (30314)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (30297)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (30312)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (30298)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (30316)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (30310)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (30315)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (30313)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (30303)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (30318)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (30307)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (30319)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (30304)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (30320)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (30302)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (30305)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (30296)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (30311)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (30296)Refutation not found, incomplete strategy% (30296)------------------------------
% 0.22/0.53  % (30296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30296)Memory used [KB]: 10618
% 0.22/0.53  % (30296)Time elapsed: 0.095 s
% 0.22/0.53  % (30296)------------------------------
% 0.22/0.53  % (30296)------------------------------
% 0.22/0.53  % (30308)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (30302)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (30295)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (30317)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (30308)Refutation not found, incomplete strategy% (30308)------------------------------
% 0.22/0.54  % (30308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30308)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30308)Memory used [KB]: 6268
% 0.22/0.54  % (30308)Time elapsed: 0.122 s
% 0.22/0.54  % (30308)------------------------------
% 0.22/0.54  % (30308)------------------------------
% 0.22/0.55  % (30295)Refutation not found, incomplete strategy% (30295)------------------------------
% 0.22/0.55  % (30295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30295)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30295)Memory used [KB]: 10618
% 0.22/0.55  % (30295)Time elapsed: 0.128 s
% 0.22/0.55  % (30295)------------------------------
% 0.22/0.55  % (30295)------------------------------
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f356,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f301,f316])).
% 0.22/0.55  fof(f316,plain,(
% 0.22/0.55    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f315,f258])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    k1_xboole_0 = sK2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f220,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.55  fof(f220,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f121,f211,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | r2_hidden(sK12(X0,X1,X2),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f210,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f107,f205,f122,f121,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 0.22/0.55    inference(backward_demodulation,[],[f105,f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f118,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    sK2 = sK9(sK0,sK1,sK2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f33,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sK9(X0,X1,X3) = X3) )),
% 0.22/0.55    inference(equality_resolution,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (sK9(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(negated_conjecture,[],[f14])).
% 0.22/0.55  fof(f14,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK9(sK0,sK1,sK2))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f33,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | k1_relat_1(sK9(X0,X1,X3)) = X0) )),
% 0.22/0.55    inference(equality_resolution,[],[f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK9(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.55    inference(backward_demodulation,[],[f95,f104])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    v1_funct_2(sK9(sK0,sK1,sK2),k1_relat_1(sK9(sK0,sK1,sK2)),k2_relat_1(sK9(sK0,sK1,sK2)))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f93,f94,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    v1_relat_1(sK9(sK0,sK1,sK2))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f33,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (v1_relat_1(sK9(X0,X1,X3)) | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK9(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    v1_funct_1(sK9(sK0,sK1,sK2))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f33,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (v1_funct_1(sK9(X0,X1,X3)) | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK9(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    ~v1_partfun1(sK2,sK0)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f107,f202,f203,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f107,f202,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(forward_demodulation,[],[f199,f119])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f106,f115,f70,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f114,f104])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f33,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f94,f104])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f93,f104])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.22/0.55    inference(backward_demodulation,[],[f111,f119])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f107,f106,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f315,plain,(
% 0.22/0.55    ( ! [X1] : (v1_funct_2(sK2,k1_xboole_0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f314,f288])).
% 0.22/0.55  fof(f288,plain,(
% 0.22/0.55    k1_xboole_0 = sK0),
% 0.22/0.55    inference(forward_demodulation,[],[f268,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f96,f38])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f88,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f34,f37])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    sK0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f119,f258])).
% 0.22/0.55  fof(f314,plain,(
% 0.22/0.55    ( ! [X1] : (v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f313,f88])).
% 0.22/0.55  fof(f313,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK7(k1_xboole_0,X1,k1_xboole_0),k1_xboole_0) | v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f281,f288])).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK7(sK0,X1,k1_xboole_0),sK0) | v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f253,f258])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK7(sK0,X1,sK2),sK0) | v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f252,f106])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK7(sK0,X1,sK2),sK0) | ~v1_relat_1(sK2) | v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f250,f107])).
% 0.22/0.55  fof(f250,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK7(sK0,X1,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v1_funct_2(sK2,sK0,X1)) )),
% 0.22/0.55    inference(superposition,[],[f75,f119])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | v1_funct_2(X2,k1_relat_1(X2),X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK7(X0,X1,X2),X0) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.22/0.55  fof(f301,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f300,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f70,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f300,plain,(
% 0.22/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f299,f144])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f142,f38])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f88,f90,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | r2_hidden(sK11(X0,X1,X2),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f299,plain,(
% 0.22/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f298,f288])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f297,f267])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f107,f258])).
% 0.22/0.55  fof(f297,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f287,f288])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(forward_demodulation,[],[f286,f258])).
% 0.22/0.55  fof(f286,plain,(
% 0.22/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f263,f258])).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(backward_demodulation,[],[f32,f258])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (30302)------------------------------
% 0.22/0.55  % (30302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30302)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (30302)Memory used [KB]: 1791
% 0.22/0.55  % (30302)Time elapsed: 0.124 s
% 0.22/0.55  % (30302)------------------------------
% 0.22/0.55  % (30302)------------------------------
% 0.22/0.55  % (30294)Success in time 0.18 s
%------------------------------------------------------------------------------
