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
% DateTime   : Thu Dec  3 12:57:48 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 688 expanded)
%              Number of leaves         :   16 ( 143 expanded)
%              Depth                    :   21
%              Number of atoms          :  200 (1968 expanded)
%              Number of equality atoms :   43 ( 353 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1049,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1040,f907])).

fof(f907,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f618,f904])).

fof(f904,plain,(
    k2_relset_1(sK1,sK0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f57,f617])).

fof(f617,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f34,f616])).

fof(f616,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f615,f594])).

fof(f594,plain,
    ( r2_hidden(sK3(sK2),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f590,f82])).

fof(f82,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f590,plain,
    ( r2_hidden(sK3(sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f421,f557])).

fof(f557,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f552,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f552,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f551,f491])).

fof(f491,plain,(
    ! [X6] :
      ( r2_hidden(sK5(k1_relat_1(sK2),X6),sK1)
      | r1_tarski(k1_relat_1(sK2),X6) ) ),
    inference(resolution,[],[f105,f112])).

fof(f112,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f111,f82])).

fof(f111,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f106,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f59,f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f551,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_relat_1(sK2),X0),sK1)
      | r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f547,f539])).

fof(f539,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f56,f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f547,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),X0)
      | ~ r2_hidden(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1) ) ),
    inference(backward_demodulation,[],[f442,f539])).

fof(f442,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1)
      | r1_tarski(k1_relset_1(sK1,sK0,sK2),X0) ) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1)
      | r1_tarski(k1_relset_1(sK1,sK0,sK2),X0) ) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f421,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f37,f61])).

fof(f61,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f615,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_hidden(sK3(sK2),k1_xboole_0) ),
    inference(resolution,[],[f600,f595])).

fof(f595,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f571,f43])).

fof(f571,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f544,f557])).

fof(f544,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f33,f539])).

fof(f600,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2),X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f599,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f599,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | r2_hidden(sK3(sK2),X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f594,f44])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f618,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f616])).

fof(f35,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f1040,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f1035,f39])).

fof(f1035,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f1018,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1018,plain,(
    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1010,f966])).

fof(f966,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k2_relset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f964,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f964,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1) ) ),
    inference(resolution,[],[f905,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f905,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1) ) ),
    inference(superposition,[],[f57,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1010,plain,(
    ! [X0] : m1_subset_1(k2_relset_1(X0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f1008,f79])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | m1_subset_1(k2_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f983,f51])).

fof(f983,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k2_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f58,f62])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (11929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11936)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (11928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11952)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (11947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (11935)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (11938)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11944)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (11927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.53  % (11953)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (11943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.53  % (11949)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (11954)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (11924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (11950)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (11951)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (11937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (11941)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (11939)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (11945)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (11940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (11925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (11934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.55  % (11933)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.55  % (11931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.55  % (11942)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.55  % (11948)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (11932)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.56  % (11932)Refutation not found, incomplete strategy% (11932)------------------------------
% 1.49/0.56  % (11932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (11932)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (11932)Memory used [KB]: 10746
% 1.49/0.56  % (11932)Time elapsed: 0.158 s
% 1.49/0.56  % (11932)------------------------------
% 1.49/0.56  % (11932)------------------------------
% 1.49/0.57  % (11930)Refutation found. Thanks to Tanya!
% 1.49/0.57  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f1049,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(subsumption_resolution,[],[f1040,f907])).
% 1.49/0.57  fof(f907,plain,(
% 1.49/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.49/0.57    inference(superposition,[],[f618,f904])).
% 1.49/0.57  fof(f904,plain,(
% 1.49/0.57    k2_relset_1(sK1,sK0,k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 1.49/0.57    inference(resolution,[],[f57,f617])).
% 1.49/0.57  fof(f617,plain,(
% 1.49/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.49/0.57    inference(backward_demodulation,[],[f34,f616])).
% 1.49/0.57  fof(f616,plain,(
% 1.49/0.57    k1_xboole_0 = sK2),
% 1.49/0.57    inference(subsumption_resolution,[],[f615,f594])).
% 1.49/0.57  fof(f594,plain,(
% 1.49/0.57    r2_hidden(sK3(sK2),k1_xboole_0) | k1_xboole_0 = sK2),
% 1.49/0.57    inference(subsumption_resolution,[],[f590,f82])).
% 1.49/0.57  fof(f82,plain,(
% 1.49/0.57    v1_relat_1(sK2)),
% 1.49/0.57    inference(resolution,[],[f70,f34])).
% 1.49/0.57  fof(f70,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.49/0.57    inference(resolution,[],[f38,f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f10])).
% 1.49/0.57  fof(f10,axiom,(
% 1.49/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.57  fof(f38,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,axiom,(
% 1.49/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.49/0.57  fof(f590,plain,(
% 1.49/0.57    r2_hidden(sK3(sK2),k1_xboole_0) | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.49/0.57    inference(superposition,[],[f421,f557])).
% 1.49/0.57  fof(f557,plain,(
% 1.49/0.57    k1_xboole_0 = k1_relat_1(sK2)),
% 1.49/0.57    inference(resolution,[],[f552,f39])).
% 1.49/0.57  fof(f39,plain,(
% 1.49/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.49/0.57    inference(ennf_transformation,[],[f3])).
% 1.49/0.57  fof(f3,axiom,(
% 1.49/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.49/0.57  fof(f552,plain,(
% 1.49/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f551,f491])).
% 1.49/0.57  fof(f491,plain,(
% 1.49/0.57    ( ! [X6] : (r2_hidden(sK5(k1_relat_1(sK2),X6),sK1) | r1_tarski(k1_relat_1(sK2),X6)) )),
% 1.49/0.57    inference(resolution,[],[f105,f112])).
% 1.49/0.57  fof(f112,plain,(
% 1.49/0.57    r1_tarski(k1_relat_1(sK2),sK1)),
% 1.49/0.57    inference(subsumption_resolution,[],[f111,f82])).
% 1.49/0.57  fof(f111,plain,(
% 1.49/0.57    r1_tarski(k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 1.49/0.57    inference(resolution,[],[f106,f42])).
% 1.49/0.57  fof(f42,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.49/0.57  fof(f106,plain,(
% 1.49/0.57    v4_relat_1(sK2,sK1)),
% 1.49/0.57    inference(resolution,[],[f59,f34])).
% 1.49/0.57  fof(f59,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f32])).
% 1.49/0.57  fof(f32,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f19])).
% 1.49/0.57  fof(f19,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.49/0.57    inference(pure_predicate_removal,[],[f12])).
% 1.49/0.57  fof(f12,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.57  fof(f105,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(resolution,[],[f44,f45])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.57  fof(f44,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f551,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(sK5(k1_relat_1(sK2),X0),sK1) | r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.49/0.57    inference(forward_demodulation,[],[f547,f539])).
% 1.49/0.57  fof(f539,plain,(
% 1.49/0.57    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.49/0.57    inference(resolution,[],[f56,f34])).
% 1.49/0.57  fof(f56,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f14])).
% 1.49/0.57  fof(f14,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.57  fof(f547,plain,(
% 1.49/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~r2_hidden(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1)) )),
% 1.49/0.57    inference(backward_demodulation,[],[f442,f539])).
% 1.49/0.57  fof(f442,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1) | r1_tarski(k1_relset_1(sK1,sK0,sK2),X0)) )),
% 1.49/0.57    inference(resolution,[],[f75,f43])).
% 1.49/0.57  fof(f43,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f5])).
% 1.49/0.57  fof(f5,axiom,(
% 1.49/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.49/0.57  fof(f75,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(sK5(k1_relset_1(sK1,sK0,sK2),X0),sK1) | r1_tarski(k1_relset_1(sK1,sK0,sK2),X0)) )),
% 1.49/0.57    inference(resolution,[],[f45,f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.49/0.57    inference(flattening,[],[f20])).
% 1.49/0.57  fof(f20,plain,(
% 1.49/0.57    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.49/0.57    inference(ennf_transformation,[],[f18])).
% 1.49/0.57  fof(f18,plain,(
% 1.49/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 1.49/0.57    inference(pure_predicate_removal,[],[f17])).
% 1.49/0.57  fof(f17,negated_conjecture,(
% 1.49/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.49/0.57    inference(negated_conjecture,[],[f16])).
% 1.49/0.57  fof(f16,conjecture,(
% 1.49/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 1.49/0.57  fof(f421,plain,(
% 1.49/0.57    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(X0)) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.49/0.57    inference(resolution,[],[f37,f61])).
% 1.49/0.57  fof(f61,plain,(
% 1.49/0.57    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.49/0.57    inference(equality_resolution,[],[f47])).
% 1.49/0.57  fof(f47,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.49/0.57    inference(cnf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.49/0.57  fof(f37,plain,(
% 1.49/0.57    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f23])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.49/0.57    inference(flattening,[],[f22])).
% 1.49/0.57  fof(f22,plain,(
% 1.49/0.57    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f11])).
% 1.49/0.57  fof(f11,axiom,(
% 1.49/0.57    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.49/0.57  fof(f615,plain,(
% 1.49/0.57    k1_xboole_0 = sK2 | ~r2_hidden(sK3(sK2),k1_xboole_0)),
% 1.49/0.57    inference(resolution,[],[f600,f595])).
% 1.49/0.57  fof(f595,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.49/0.57    inference(resolution,[],[f571,f43])).
% 1.49/0.57  fof(f571,plain,(
% 1.49/0.57    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_xboole_0)) )),
% 1.49/0.57    inference(backward_demodulation,[],[f544,f557])).
% 1.49/0.57  fof(f544,plain,(
% 1.49/0.57    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.49/0.57    inference(backward_demodulation,[],[f33,f539])).
% 1.49/0.57  fof(f600,plain,(
% 1.49/0.57    ( ! [X0] : (r2_hidden(sK3(sK2),X0) | k1_xboole_0 = sK2) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f599,f36])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.57  fof(f599,plain,(
% 1.49/0.57    ( ! [X0] : (k1_xboole_0 = sK2 | r2_hidden(sK3(sK2),X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.57    inference(resolution,[],[f594,f44])).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f57,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f15])).
% 1.49/0.57  fof(f15,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.49/0.57  fof(f618,plain,(
% 1.49/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,k1_xboole_0)),
% 1.49/0.57    inference(backward_demodulation,[],[f35,f616])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f1040,plain,(
% 1.49/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.49/0.57    inference(resolution,[],[f1035,f39])).
% 1.49/0.57  fof(f1035,plain,(
% 1.49/0.57    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.49/0.57    inference(resolution,[],[f1018,f52])).
% 1.49/0.57  fof(f52,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.57  fof(f1018,plain,(
% 1.49/0.57    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.49/0.57    inference(forward_demodulation,[],[f1010,f966])).
% 1.49/0.57  fof(f966,plain,(
% 1.49/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relset_1(X0,k1_xboole_0,k1_xboole_0)) )),
% 1.49/0.57    inference(resolution,[],[f964,f79])).
% 1.49/0.57  fof(f79,plain,(
% 1.49/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.49/0.57    inference(duplicate_literal_removal,[],[f78])).
% 1.49/0.57  fof(f78,plain,(
% 1.49/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.49/0.57    inference(resolution,[],[f46,f45])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f964,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)) )),
% 1.49/0.57    inference(resolution,[],[f905,f51])).
% 1.49/0.57  fof(f51,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f6])).
% 1.49/0.57  fof(f905,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)) )),
% 1.49/0.57    inference(superposition,[],[f57,f62])).
% 1.49/0.57  fof(f62,plain,(
% 1.49/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.49/0.57    inference(equality_resolution,[],[f55])).
% 1.49/0.57  fof(f55,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.49/0.57  fof(f1010,plain,(
% 1.49/0.57    ( ! [X0] : (m1_subset_1(k2_relset_1(X0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.49/0.57    inference(resolution,[],[f1008,f79])).
% 1.49/0.57  fof(f1008,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | m1_subset_1(k2_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.49/0.57    inference(resolution,[],[f983,f51])).
% 1.49/0.57  fof(f983,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_relset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.49/0.57    inference(superposition,[],[f58,f62])).
% 1.49/0.57  fof(f58,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f31])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f13])).
% 1.49/0.57  fof(f13,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (11930)------------------------------
% 1.49/0.57  % (11930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (11930)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (11930)Memory used [KB]: 6652
% 1.49/0.57  % (11930)Time elapsed: 0.104 s
% 1.49/0.57  % (11930)------------------------------
% 1.49/0.57  % (11930)------------------------------
% 1.49/0.58  % (11919)Success in time 0.219 s
%------------------------------------------------------------------------------
