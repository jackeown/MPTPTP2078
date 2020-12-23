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
% DateTime   : Thu Dec  3 12:43:48 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  100 (4715 expanded)
%              Number of leaves         :    9 (1141 expanded)
%              Depth                    :   33
%              Number of atoms          :  262 (18404 expanded)
%              Number of equality atoms :   57 (2389 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1312,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1305,f1310])).

fof(f1310,plain,(
    sK1 != k7_subset_1(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f1123,f1206])).

fof(f1206,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f1112,f1113])).

fof(f1113,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f1042,f877])).

fof(f877,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(subsumption_resolution,[],[f875,f20])).

fof(f20,plain,(
    sK1 != k7_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(f875,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = k7_subset_1(sK0,sK2,sK3) ) ),
    inference(resolution,[],[f862,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f862,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X1,sK0)
      | sK1 = k7_subset_1(X0,sK2,sK3) ) ),
    inference(superposition,[],[f861,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f861,plain,(
    ! [X2] :
      ( sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f860,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f860,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f854,f605])).

fof(f605,plain,(
    ! [X7] :
      ( sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
      | r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | ~ r2_hidden(X7,sK0) ) ),
    inference(duplicate_literal_removal,[],[f602])).

fof(f602,plain,(
    ! [X7] :
      ( r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
      | ~ r2_hidden(X7,sK0)
      | r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ) ),
    inference(resolution,[],[f202,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f41,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f202,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK7(sK2,X3,sK1),sK3)
      | r2_hidden(sK7(sK2,X3,sK1),sK1)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,X3))
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f198,f113])).

fof(f113,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f100,f25])).

fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f99,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f68,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f59,f23])).

fof(f23,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f59,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f18,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f198,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK2,X0,sK1),sK2)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ) ),
    inference(factoring,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK1),sK2)
      | r2_hidden(sK7(X0,X1,sK1),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1 ) ),
    inference(resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f83,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f73,f31])).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f61,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f22,f30])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f16,f29])).

fof(f16,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f854,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
      | ~ r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f633,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f77])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f17,f29])).

fof(f17,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f633,plain,(
    ! [X14] :
      ( r2_hidden(sK7(sK2,sK3,sK1),sK3)
      | ~ r2_hidden(X14,sK0)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f631,f103])).

fof(f631,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK0)
      | r2_hidden(sK7(sK2,sK3,sK1),sK3)
      | ~ r2_hidden(sK7(sK2,sK3,sK1),sK2)
      | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ) ),
    inference(resolution,[],[f621,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f621,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f619,f20])).

fof(f619,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | ~ r2_hidden(X0,sK0)
      | sK1 = k7_subset_1(sK0,sK2,sK3) ) ),
    inference(resolution,[],[f606,f21])).

fof(f606,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r2_hidden(sK7(sK2,sK3,sK1),sK1)
      | ~ r2_hidden(X1,sK0)
      | sK1 = k7_subset_1(X0,sK2,sK3) ) ),
    inference(superposition,[],[f605,f45])).

fof(f1042,plain,(
    ! [X0] :
      ( sK1 = sK3
      | r2_hidden(sK7(sK0,X0,sK1),sK0) ) ),
    inference(backward_demodulation,[],[f457,f896])).

fof(f896,plain,(
    ! [X17] : sK3 = k5_xboole_0(sK0,k3_xboole_0(sK0,X17)) ),
    inference(resolution,[],[f877,f401])).

fof(f401,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK3),sK0)
      | sK3 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(factoring,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK3),sK0)
      | r2_hidden(sK7(X0,X1,sK3),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3 ) ),
    inference(resolution,[],[f67,f50])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f58,f52])).

fof(f58,plain,(
    r2_hidden(sK3,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f57,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f19,f30])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f457,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK1),sK0)
      | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(factoring,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK1),sK0)
      | r2_hidden(sK7(X0,X1,sK1),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1 ) ),
    inference(resolution,[],[f77,f50])).

fof(f1112,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f1040,f877])).

fof(f1040,plain,(
    ! [X0] :
      ( sK2 = sK3
      | r2_hidden(sK7(sK0,X0,sK2),sK0) ) ),
    inference(backward_demodulation,[],[f419,f896])).

fof(f419,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK2),sK0)
      | sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ) ),
    inference(factoring,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK2),sK0)
      | r2_hidden(sK7(X0,X1,sK2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK2 ) ),
    inference(resolution,[],[f72,f50])).

fof(f1123,plain,(
    sK1 != k7_subset_1(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f20,f1112])).

fof(f1305,plain,(
    sK1 = k7_subset_1(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f1304,f1206])).

fof(f1304,plain,(
    sK1 = k7_subset_1(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f1254,f916])).

fof(f916,plain,(
    ! [X3] : ~ r2_hidden(X3,sK1) ),
    inference(resolution,[],[f890,f25])).

fof(f890,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f877,f84])).

fof(f84,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f77,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1254,plain,
    ( r2_hidden(sK7(sK1,sK1,sK1),sK1)
    | sK1 = k7_subset_1(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f294,f1206])).

fof(f294,plain,
    ( sK1 = k7_subset_1(sK0,sK2,sK2)
    | r2_hidden(sK7(sK2,sK2,sK1),sK1) ),
    inference(resolution,[],[f212,f21])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r2_hidden(sK7(sK2,sK2,sK1),sK1)
      | sK1 = k7_subset_1(X0,sK2,sK2) ) ),
    inference(superposition,[],[f207,f45])).

fof(f207,plain,
    ( sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | r2_hidden(sK7(sK2,sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | r2_hidden(sK7(sK2,sK2,sK1),sK1)
    | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) ),
    inference(resolution,[],[f198,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:07:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (13224)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (13241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (13218)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (13242)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (13216)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (13217)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13233)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (13234)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (13236)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (13213)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (13226)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (13228)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (13215)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13214)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (13223)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13219)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (13240)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (13239)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (13238)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (13237)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13243)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (13230)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (13229)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13236)Refutation not found, incomplete strategy% (13236)------------------------------
% 0.21/0.53  % (13236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13236)Memory used [KB]: 10874
% 0.21/0.53  % (13236)Time elapsed: 0.094 s
% 0.21/0.53  % (13236)------------------------------
% 0.21/0.53  % (13236)------------------------------
% 0.21/0.53  % (13232)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13231)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (13235)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (13221)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (13220)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (13222)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (13223)Refutation not found, incomplete strategy% (13223)------------------------------
% 0.21/0.55  % (13223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13223)Memory used [KB]: 10618
% 0.21/0.55  % (13223)Time elapsed: 0.153 s
% 0.21/0.55  % (13223)------------------------------
% 0.21/0.55  % (13223)------------------------------
% 0.21/0.55  % (13227)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.12/0.65  % (13235)Refutation found. Thanks to Tanya!
% 2.12/0.65  % SZS status Theorem for theBenchmark
% 2.12/0.65  % SZS output start Proof for theBenchmark
% 2.12/0.65  fof(f1312,plain,(
% 2.12/0.65    $false),
% 2.12/0.65    inference(subsumption_resolution,[],[f1305,f1310])).
% 2.12/0.65  fof(f1310,plain,(
% 2.12/0.65    sK1 != k7_subset_1(sK0,sK1,sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f1123,f1206])).
% 2.12/0.65  fof(f1206,plain,(
% 2.12/0.65    sK1 = sK2),
% 2.12/0.65    inference(backward_demodulation,[],[f1112,f1113])).
% 2.12/0.65  fof(f1113,plain,(
% 2.12/0.65    sK1 = sK3),
% 2.12/0.65    inference(subsumption_resolution,[],[f1042,f877])).
% 2.12/0.65  fof(f877,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f875,f20])).
% 2.12/0.65  fof(f20,plain,(
% 2.12/0.65    sK1 != k7_subset_1(sK0,sK2,sK3)),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f12,plain,(
% 2.12/0.65    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.65    inference(flattening,[],[f11])).
% 2.12/0.65  fof(f11,plain,(
% 2.12/0.65    ? [X0,X1] : (? [X2] : (? [X3] : ((k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.65    inference(ennf_transformation,[],[f10])).
% 2.12/0.65  fof(f10,negated_conjecture,(
% 2.12/0.65    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 2.12/0.65    inference(negated_conjecture,[],[f9])).
% 2.12/0.65  fof(f9,conjecture,(
% 2.12/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).
% 2.12/0.65  fof(f875,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k7_subset_1(sK0,sK2,sK3)) )),
% 2.12/0.65    inference(resolution,[],[f862,f21])).
% 2.12/0.65  fof(f21,plain,(
% 2.12/0.65    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f862,plain,(
% 2.12/0.65    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r2_hidden(X1,sK0) | sK1 = k7_subset_1(X0,sK2,sK3)) )),
% 2.12/0.65    inference(superposition,[],[f861,f45])).
% 2.12/0.65  fof(f45,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f38,f26])).
% 2.12/0.65  fof(f26,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f4])).
% 2.12/0.65  fof(f4,axiom,(
% 2.12/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.65  fof(f38,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f15])).
% 2.12/0.65  fof(f15,plain,(
% 2.12/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.65    inference(ennf_transformation,[],[f8])).
% 2.12/0.65  fof(f8,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.12/0.65  fof(f861,plain,(
% 2.12/0.65    ( ! [X2] : (sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) | ~r2_hidden(X2,sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f860,f25])).
% 2.12/0.65  fof(f25,plain,(
% 2.12/0.65    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f1])).
% 2.12/0.65  fof(f1,axiom,(
% 2.12/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.12/0.65  fof(f860,plain,(
% 2.12/0.65    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f854,f605])).
% 2.12/0.65  fof(f605,plain,(
% 2.12/0.65    ( ! [X7] : (sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) | r2_hidden(sK7(sK2,sK3,sK1),sK1) | ~r2_hidden(X7,sK0)) )),
% 2.12/0.65    inference(duplicate_literal_removal,[],[f602])).
% 2.12/0.65  fof(f602,plain,(
% 2.12/0.65    ( ! [X7] : (r2_hidden(sK7(sK2,sK3,sK1),sK1) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) | ~r2_hidden(X7,sK0) | r2_hidden(sK7(sK2,sK3,sK1),sK1) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) )),
% 2.12/0.65    inference(resolution,[],[f202,f49])).
% 2.12/0.65  fof(f49,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.12/0.65    inference(definition_unfolding,[],[f41,f26])).
% 2.12/0.65  fof(f41,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.12/0.65    inference(cnf_transformation,[],[f3])).
% 2.12/0.65  fof(f3,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.12/0.65  fof(f202,plain,(
% 2.12/0.65    ( ! [X4,X3] : (r2_hidden(sK7(sK2,X3,sK1),sK3) | r2_hidden(sK7(sK2,X3,sK1),sK1) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,X3)) | ~r2_hidden(X4,sK0)) )),
% 2.12/0.65    inference(resolution,[],[f198,f113])).
% 2.12/0.65  fof(f113,plain,(
% 2.12/0.65    ( ! [X4,X5] : (~r2_hidden(X4,sK2) | r2_hidden(X4,sK1) | r2_hidden(X4,sK3) | ~r2_hidden(X5,sK0)) )),
% 2.12/0.65    inference(resolution,[],[f100,f25])).
% 2.12/0.65  fof(f100,plain,(
% 2.12/0.65    ( ! [X0] : (v1_xboole_0(sK0) | r2_hidden(X0,sK3) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f99,f72])).
% 2.12/0.65  fof(f72,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(resolution,[],[f68,f31])).
% 2.12/0.65  fof(f31,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f14])).
% 2.12/0.65  fof(f14,plain,(
% 2.12/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.12/0.65    inference(ennf_transformation,[],[f2])).
% 2.12/0.65  fof(f2,axiom,(
% 2.12/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.12/0.65  fof(f68,plain,(
% 2.12/0.65    r1_tarski(sK2,sK0)),
% 2.12/0.65    inference(resolution,[],[f60,f52])).
% 2.12/0.65  fof(f52,plain,(
% 2.12/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.12/0.65    inference(equality_resolution,[],[f35])).
% 2.12/0.65  fof(f35,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.12/0.65    inference(cnf_transformation,[],[f5])).
% 2.12/0.65  fof(f5,axiom,(
% 2.12/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.12/0.65  fof(f60,plain,(
% 2.12/0.65    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(subsumption_resolution,[],[f59,f23])).
% 2.12/0.65  fof(f23,plain,(
% 2.12/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f7])).
% 2.12/0.65  fof(f7,axiom,(
% 2.12/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.12/0.65  fof(f59,plain,(
% 2.12/0.65    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(resolution,[],[f21,f30])).
% 2.12/0.65  fof(f30,plain,(
% 2.12/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f13])).
% 2.12/0.65  fof(f13,plain,(
% 2.12/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.12/0.65    inference(ennf_transformation,[],[f6])).
% 2.12/0.65  fof(f6,axiom,(
% 2.12/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.12/0.65  fof(f99,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK3) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(resolution,[],[f18,f29])).
% 2.12/0.65  fof(f29,plain,(
% 2.12/0.65    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f13])).
% 2.12/0.65  fof(f18,plain,(
% 2.12/0.65    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f198,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK2,X0,sK1),sK2) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) )),
% 2.12/0.65    inference(factoring,[],[f103])).
% 2.12/0.65  fof(f103,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK1),sK2) | r2_hidden(sK7(X0,X1,sK1),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1) )),
% 2.12/0.65    inference(resolution,[],[f101,f50])).
% 2.12/0.65  fof(f50,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.12/0.65    inference(definition_unfolding,[],[f40,f26])).
% 2.12/0.65  fof(f40,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.12/0.65    inference(cnf_transformation,[],[f3])).
% 2.12/0.65  fof(f101,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f83,f77])).
% 2.12/0.65  fof(f77,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(resolution,[],[f73,f31])).
% 2.12/0.65  fof(f73,plain,(
% 2.12/0.65    r1_tarski(sK1,sK0)),
% 2.12/0.65    inference(resolution,[],[f62,f52])).
% 2.12/0.65  fof(f62,plain,(
% 2.12/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(subsumption_resolution,[],[f61,f23])).
% 2.12/0.65  fof(f61,plain,(
% 2.12/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(resolution,[],[f22,f30])).
% 2.12/0.65  fof(f22,plain,(
% 2.12/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f83,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f82,f25])).
% 2.12/0.65  fof(f82,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(resolution,[],[f16,f29])).
% 2.12/0.65  fof(f16,plain,(
% 2.12/0.65    ( ! [X4] : (~m1_subset_1(X4,sK0) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f854,plain,(
% 2.12/0.65    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) | ~r2_hidden(sK7(sK2,sK3,sK1),sK1) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(resolution,[],[f633,f96])).
% 2.12/0.65  fof(f96,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f95,f77])).
% 2.12/0.65  fof(f95,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 2.12/0.65    inference(resolution,[],[f17,f29])).
% 2.12/0.65  fof(f17,plain,(
% 2.12/0.65    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | ~r2_hidden(X4,sK1)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f633,plain,(
% 2.12/0.65    ( ! [X14] : (r2_hidden(sK7(sK2,sK3,sK1),sK3) | ~r2_hidden(X14,sK0) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f631,f103])).
% 2.12/0.65  fof(f631,plain,(
% 2.12/0.65    ( ! [X14] : (~r2_hidden(X14,sK0) | r2_hidden(sK7(sK2,sK3,sK1),sK3) | ~r2_hidden(sK7(sK2,sK3,sK1),sK2) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) )),
% 2.12/0.65    inference(resolution,[],[f621,f51])).
% 2.12/0.65  fof(f51,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.12/0.65    inference(definition_unfolding,[],[f39,f26])).
% 2.12/0.65  fof(f39,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.12/0.65    inference(cnf_transformation,[],[f3])).
% 2.12/0.65  fof(f621,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK2,sK3,sK1),sK1) | ~r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f619,f20])).
% 2.12/0.65  fof(f619,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK2,sK3,sK1),sK1) | ~r2_hidden(X0,sK0) | sK1 = k7_subset_1(sK0,sK2,sK3)) )),
% 2.12/0.65    inference(resolution,[],[f606,f21])).
% 2.12/0.65  fof(f606,plain,(
% 2.12/0.65    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r2_hidden(sK7(sK2,sK3,sK1),sK1) | ~r2_hidden(X1,sK0) | sK1 = k7_subset_1(X0,sK2,sK3)) )),
% 2.12/0.65    inference(superposition,[],[f605,f45])).
% 2.12/0.65  fof(f1042,plain,(
% 2.12/0.65    ( ! [X0] : (sK1 = sK3 | r2_hidden(sK7(sK0,X0,sK1),sK0)) )),
% 2.12/0.65    inference(backward_demodulation,[],[f457,f896])).
% 2.12/0.65  fof(f896,plain,(
% 2.12/0.65    ( ! [X17] : (sK3 = k5_xboole_0(sK0,k3_xboole_0(sK0,X17))) )),
% 2.12/0.65    inference(resolution,[],[f877,f401])).
% 2.12/0.65  fof(f401,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK0,X0,sK3),sK0) | sK3 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 2.12/0.65    inference(factoring,[],[f79])).
% 2.12/0.65  fof(f79,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK3),sK0) | r2_hidden(sK7(X0,X1,sK3),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3) )),
% 2.12/0.65    inference(resolution,[],[f67,f50])).
% 2.12/0.65  fof(f67,plain,(
% 2.12/0.65    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK0)) )),
% 2.12/0.65    inference(resolution,[],[f63,f31])).
% 2.12/0.65  fof(f63,plain,(
% 2.12/0.65    r1_tarski(sK3,sK0)),
% 2.12/0.65    inference(resolution,[],[f58,f52])).
% 2.12/0.65  fof(f58,plain,(
% 2.12/0.65    r2_hidden(sK3,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(subsumption_resolution,[],[f57,f23])).
% 2.12/0.65  fof(f57,plain,(
% 2.12/0.65    r2_hidden(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(resolution,[],[f19,f30])).
% 2.12/0.65  fof(f19,plain,(
% 2.12/0.65    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f457,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK0,X0,sK1),sK0) | sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 2.12/0.65    inference(factoring,[],[f85])).
% 2.12/0.65  fof(f85,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK1),sK0) | r2_hidden(sK7(X0,X1,sK1),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK1) )),
% 2.12/0.65    inference(resolution,[],[f77,f50])).
% 2.12/0.65  fof(f1112,plain,(
% 2.12/0.65    sK2 = sK3),
% 2.12/0.65    inference(subsumption_resolution,[],[f1040,f877])).
% 2.12/0.65  fof(f1040,plain,(
% 2.12/0.65    ( ! [X0] : (sK2 = sK3 | r2_hidden(sK7(sK0,X0,sK2),sK0)) )),
% 2.12/0.65    inference(backward_demodulation,[],[f419,f896])).
% 2.12/0.65  fof(f419,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK7(sK0,X0,sK2),sK0) | sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 2.12/0.65    inference(factoring,[],[f81])).
% 2.12/0.65  fof(f81,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK2),sK0) | r2_hidden(sK7(X0,X1,sK2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK2) )),
% 2.12/0.65    inference(resolution,[],[f72,f50])).
% 2.12/0.65  fof(f1123,plain,(
% 2.12/0.65    sK1 != k7_subset_1(sK0,sK2,sK2)),
% 2.12/0.65    inference(backward_demodulation,[],[f20,f1112])).
% 2.12/0.65  fof(f1305,plain,(
% 2.12/0.65    sK1 = k7_subset_1(sK0,sK1,sK1)),
% 2.12/0.65    inference(forward_demodulation,[],[f1304,f1206])).
% 2.12/0.65  fof(f1304,plain,(
% 2.12/0.65    sK1 = k7_subset_1(sK0,sK2,sK2)),
% 2.12/0.65    inference(subsumption_resolution,[],[f1254,f916])).
% 2.12/0.65  fof(f916,plain,(
% 2.12/0.65    ( ! [X3] : (~r2_hidden(X3,sK1)) )),
% 2.12/0.65    inference(resolution,[],[f890,f25])).
% 2.12/0.65  fof(f890,plain,(
% 2.12/0.65    v1_xboole_0(sK1)),
% 2.12/0.65    inference(resolution,[],[f877,f84])).
% 2.12/0.65  fof(f84,plain,(
% 2.12/0.65    r2_hidden(sK4(sK1),sK0) | v1_xboole_0(sK1)),
% 2.12/0.65    inference(resolution,[],[f77,f24])).
% 2.12/0.65  fof(f24,plain,(
% 2.12/0.65    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f1])).
% 2.12/0.65  fof(f1254,plain,(
% 2.12/0.65    r2_hidden(sK7(sK1,sK1,sK1),sK1) | sK1 = k7_subset_1(sK0,sK2,sK2)),
% 2.12/0.65    inference(backward_demodulation,[],[f294,f1206])).
% 2.12/0.65  fof(f294,plain,(
% 2.12/0.65    sK1 = k7_subset_1(sK0,sK2,sK2) | r2_hidden(sK7(sK2,sK2,sK1),sK1)),
% 2.12/0.65    inference(resolution,[],[f212,f21])).
% 2.12/0.65  fof(f212,plain,(
% 2.12/0.65    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r2_hidden(sK7(sK2,sK2,sK1),sK1) | sK1 = k7_subset_1(X0,sK2,sK2)) )),
% 2.12/0.65    inference(superposition,[],[f207,f45])).
% 2.12/0.65  fof(f207,plain,(
% 2.12/0.65    sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) | r2_hidden(sK7(sK2,sK2,sK1),sK1)),
% 2.12/0.65    inference(duplicate_literal_removal,[],[f204])).
% 2.12/0.65  fof(f204,plain,(
% 2.12/0.65    sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) | r2_hidden(sK7(sK2,sK2,sK1),sK1) | sK1 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))),
% 2.12/0.65    inference(resolution,[],[f198,f49])).
% 2.12/0.65  % SZS output end Proof for theBenchmark
% 2.12/0.65  % (13235)------------------------------
% 2.12/0.65  % (13235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (13235)Termination reason: Refutation
% 2.12/0.65  
% 2.12/0.65  % (13235)Memory used [KB]: 2174
% 2.12/0.65  % (13235)Time elapsed: 0.262 s
% 2.12/0.65  % (13235)------------------------------
% 2.12/0.65  % (13235)------------------------------
% 2.12/0.66  % (13212)Success in time 0.303 s
%------------------------------------------------------------------------------
