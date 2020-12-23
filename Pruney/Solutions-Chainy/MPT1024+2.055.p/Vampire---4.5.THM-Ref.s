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
% DateTime   : Thu Dec  3 13:06:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 728 expanded)
%              Number of leaves         :   12 ( 153 expanded)
%              Depth                    :   22
%              Number of atoms          :  214 (2806 expanded)
%              Number of equality atoms :   54 ( 445 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f718,plain,(
    $false ),
    inference(subsumption_resolution,[],[f592,f717])).

fof(f717,plain,(
    ! [X2] : sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3)) ),
    inference(subsumption_resolution,[],[f716,f63])).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f62,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f716,plain,(
    ! [X2] :
      ( sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f712,f30])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f712,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK3)
      | sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f371,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f371,plain,(
    ! [X13] : r2_hidden(k4_tarski(sK5(sK4,X13,sK3),sK4),sK3) ),
    inference(resolution,[],[f207,f63])).

fof(f207,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(sK4,X1,X2),sK4),X2) ) ),
    inference(resolution,[],[f190,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f190,plain,(
    ! [X0] : r2_hidden(sK4,X0) ),
    inference(resolution,[],[f173,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f173,plain,(
    r2_hidden(sK4,k1_xboole_0) ),
    inference(resolution,[],[f124,f73])).

fof(f73,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f29,f71])).

fof(f71,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f29,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f96,f117])).

fof(f117,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f115,f110])).

fof(f110,plain,(
    ~ r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f98,f109])).

fof(f109,plain,(
    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f108,f63])).

fof(f108,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f103,f30])).

fof(f103,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f50])).

fof(f79,plain,(
    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f76,f63])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f39])).

fof(f98,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    inference(resolution,[],[f81,f28])).

fof(f28,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f78,f63])).

fof(f78,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f115,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f80,f113])).

fof(f113,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f94,f65])).

fof(f65,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f92,f31])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f80,plain,(
    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f77,f63])).

fof(f77,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f74,f36])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f66,f71])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f592,plain,(
    sK4 != k1_funct_1(sK3,sK5(sK4,k1_xboole_0,sK3)) ),
    inference(subsumption_resolution,[],[f589,f449])).

fof(f449,plain,(
    ! [X0] : r2_hidden(sK5(sK4,k1_xboole_0,sK3),X0) ),
    inference(resolution,[],[f343,f67])).

fof(f343,plain,(
    ! [X13] : r2_hidden(sK5(sK4,X13,sK3),X13) ),
    inference(resolution,[],[f209,f63])).

fof(f209,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X6)
      | r2_hidden(sK5(sK4,X5,X6),X5) ) ),
    inference(resolution,[],[f190,f40])).

fof(f589,plain,
    ( ~ r2_hidden(sK5(sK4,k1_xboole_0,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK4,k1_xboole_0,sK3)) ),
    inference(resolution,[],[f449,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:12:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (13947)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (13954)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (13947)Refutation not found, incomplete strategy% (13947)------------------------------
% 0.22/0.48  % (13947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13947)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13947)Memory used [KB]: 10618
% 0.22/0.48  % (13947)Time elapsed: 0.059 s
% 0.22/0.48  % (13947)------------------------------
% 0.22/0.48  % (13947)------------------------------
% 0.22/0.49  % (13955)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (13962)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (13946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (13952)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (13950)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (13957)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (13948)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (13951)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (13949)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (13957)Refutation not found, incomplete strategy% (13957)------------------------------
% 0.22/0.53  % (13957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13957)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13957)Memory used [KB]: 10618
% 0.22/0.53  % (13957)Time elapsed: 0.107 s
% 0.22/0.53  % (13957)------------------------------
% 0.22/0.53  % (13957)------------------------------
% 0.22/0.53  % (13961)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (13953)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.54  % (13960)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.54  % (13956)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.55  % (13963)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.55  % (13965)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.55  % (13946)Refutation not found, incomplete strategy% (13946)------------------------------
% 0.22/0.55  % (13946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13946)Memory used [KB]: 6524
% 0.22/0.55  % (13946)Time elapsed: 0.094 s
% 0.22/0.55  % (13946)------------------------------
% 0.22/0.55  % (13946)------------------------------
% 0.22/0.56  % (13959)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.57  % (13958)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (13964)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.59  % (13966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.59  % (13963)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f718,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f592,f717])).
% 0.22/0.59  fof(f717,plain,(
% 0.22/0.59    ( ! [X2] : (sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f716,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    v1_relat_1(sK3)),
% 0.22/0.59    inference(subsumption_resolution,[],[f62,f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.22/0.59    inference(resolution,[],[f34,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.59    inference(flattening,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.59    inference(negated_conjecture,[],[f12])).
% 0.22/0.59  fof(f12,conjecture,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.59  fof(f716,plain,(
% 0.22/0.59    ( ! [X2] : (sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3)) | ~v1_relat_1(sK3)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f712,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    v1_funct_1(sK3)),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f712,plain,(
% 0.22/0.59    ( ! [X2] : (~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK4,X2,sK3)) | ~v1_relat_1(sK3)) )),
% 0.22/0.59    inference(resolution,[],[f371,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.59    inference(flattening,[],[f24])).
% 1.87/0.60  fof(f24,plain,(
% 1.87/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.87/0.60    inference(ennf_transformation,[],[f7])).
% 1.87/0.60  fof(f7,axiom,(
% 1.87/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.87/0.60  fof(f371,plain,(
% 1.87/0.60    ( ! [X13] : (r2_hidden(k4_tarski(sK5(sK4,X13,sK3),sK4),sK3)) )),
% 1.87/0.60    inference(resolution,[],[f207,f63])).
% 1.87/0.60  fof(f207,plain,(
% 1.87/0.60    ( ! [X2,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(sK4,X1,X2),sK4),X2)) )),
% 1.87/0.60    inference(resolution,[],[f190,f39])).
% 1.87/0.60  fof(f39,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f20])).
% 1.87/0.60  fof(f20,plain,(
% 1.87/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.87/0.60    inference(ennf_transformation,[],[f6])).
% 1.87/0.60  fof(f6,axiom,(
% 1.87/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.87/0.60  fof(f190,plain,(
% 1.87/0.60    ( ! [X0] : (r2_hidden(sK4,X0)) )),
% 1.87/0.60    inference(resolution,[],[f173,f67])).
% 1.87/0.60  fof(f67,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.87/0.60    inference(resolution,[],[f60,f36])).
% 1.87/0.60  fof(f36,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f18])).
% 1.87/0.60  fof(f18,plain,(
% 1.87/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.60    inference(ennf_transformation,[],[f2])).
% 1.87/0.60  fof(f2,axiom,(
% 1.87/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.87/0.60  fof(f60,plain,(
% 1.87/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.87/0.60    inference(resolution,[],[f37,f33])).
% 1.87/0.60  fof(f33,plain,(
% 1.87/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f1])).
% 1.87/0.60  fof(f1,axiom,(
% 1.87/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.87/0.60  fof(f37,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.87/0.60    inference(cnf_transformation,[],[f19])).
% 1.87/0.60  fof(f19,plain,(
% 1.87/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.87/0.60    inference(ennf_transformation,[],[f14])).
% 1.87/0.60  fof(f14,plain,(
% 1.87/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.87/0.60    inference(unused_predicate_definition_removal,[],[f3])).
% 1.87/0.60  fof(f3,axiom,(
% 1.87/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.87/0.60  fof(f173,plain,(
% 1.87/0.60    r2_hidden(sK4,k1_xboole_0)),
% 1.87/0.60    inference(resolution,[],[f124,f73])).
% 1.87/0.60  fof(f73,plain,(
% 1.87/0.60    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.87/0.60    inference(backward_demodulation,[],[f29,f71])).
% 1.87/0.60  fof(f71,plain,(
% 1.87/0.60    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.87/0.60    inference(resolution,[],[f53,f32])).
% 1.87/0.60  fof(f53,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f27])).
% 1.87/0.60  fof(f27,plain,(
% 1.87/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.60    inference(ennf_transformation,[],[f10])).
% 1.87/0.60  fof(f10,axiom,(
% 1.87/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.87/0.60  fof(f29,plain,(
% 1.87/0.60    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.87/0.60    inference(cnf_transformation,[],[f16])).
% 1.87/0.60  fof(f124,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.87/0.60    inference(backward_demodulation,[],[f96,f117])).
% 1.87/0.60  fof(f117,plain,(
% 1.87/0.60    k1_xboole_0 = sK1),
% 1.87/0.60    inference(subsumption_resolution,[],[f115,f110])).
% 1.87/0.60  fof(f110,plain,(
% 1.87/0.60    ~r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 1.87/0.60    inference(subsumption_resolution,[],[f98,f109])).
% 1.87/0.60  fof(f109,plain,(
% 1.87/0.60    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.87/0.60    inference(subsumption_resolution,[],[f108,f63])).
% 1.87/0.60  fof(f108,plain,(
% 1.87/0.60    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.87/0.60    inference(subsumption_resolution,[],[f103,f30])).
% 1.87/0.60  fof(f103,plain,(
% 1.87/0.60    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.87/0.60    inference(resolution,[],[f79,f50])).
% 1.87/0.60  fof(f79,plain,(
% 1.87/0.60    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 1.87/0.60    inference(subsumption_resolution,[],[f76,f63])).
% 1.87/0.60  fof(f76,plain,(
% 1.87/0.60    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.87/0.60    inference(resolution,[],[f73,f39])).
% 1.87/0.60  fof(f98,plain,(
% 1.87/0.60    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 1.87/0.60    inference(resolution,[],[f81,f28])).
% 1.87/0.60  fof(f28,plain,(
% 1.87/0.60    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f16])).
% 1.87/0.60  fof(f81,plain,(
% 1.87/0.60    r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 1.87/0.60    inference(subsumption_resolution,[],[f78,f63])).
% 1.87/0.60  fof(f78,plain,(
% 1.87/0.60    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.87/0.60    inference(resolution,[],[f73,f40])).
% 1.87/0.60  fof(f40,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f20])).
% 1.87/0.60  fof(f115,plain,(
% 1.87/0.60    r2_hidden(sK5(sK4,sK2,sK3),sK0) | k1_xboole_0 = sK1),
% 1.87/0.60    inference(superposition,[],[f80,f113])).
% 1.87/0.60  fof(f113,plain,(
% 1.87/0.60    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.87/0.60    inference(superposition,[],[f94,f65])).
% 1.87/0.60  fof(f65,plain,(
% 1.87/0.60    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.87/0.60    inference(resolution,[],[f42,f32])).
% 1.87/0.60  fof(f42,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f21])).
% 1.87/0.60  fof(f21,plain,(
% 1.87/0.60    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.60    inference(ennf_transformation,[],[f9])).
% 1.87/0.60  fof(f9,axiom,(
% 1.87/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.87/0.60  fof(f94,plain,(
% 1.87/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.87/0.60    inference(subsumption_resolution,[],[f92,f31])).
% 1.87/0.60  fof(f31,plain,(
% 1.87/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.87/0.60    inference(cnf_transformation,[],[f16])).
% 1.87/0.60  fof(f92,plain,(
% 1.87/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 1.87/0.60    inference(resolution,[],[f48,f32])).
% 1.87/0.60  fof(f48,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f23])).
% 1.87/0.60  fof(f23,plain,(
% 1.87/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.60    inference(flattening,[],[f22])).
% 1.87/0.60  fof(f22,plain,(
% 1.87/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.60    inference(ennf_transformation,[],[f11])).
% 1.87/0.60  fof(f11,axiom,(
% 1.87/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.87/0.60  fof(f80,plain,(
% 1.87/0.60    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.87/0.60    inference(subsumption_resolution,[],[f77,f63])).
% 1.87/0.60  fof(f77,plain,(
% 1.87/0.60    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.87/0.60    inference(resolution,[],[f73,f38])).
% 1.87/0.60  fof(f38,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f20])).
% 1.87/0.60  fof(f96,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(X0,sK1)) )),
% 1.87/0.60    inference(resolution,[],[f74,f36])).
% 1.87/0.60  fof(f74,plain,(
% 1.87/0.60    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.87/0.60    inference(backward_demodulation,[],[f66,f71])).
% 1.87/0.60  fof(f66,plain,(
% 1.87/0.60    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.87/0.60    inference(resolution,[],[f52,f32])).
% 1.87/0.60  fof(f52,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.87/0.60    inference(cnf_transformation,[],[f26])).
% 1.87/0.60  fof(f26,plain,(
% 1.87/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.60    inference(ennf_transformation,[],[f8])).
% 1.87/0.60  fof(f8,axiom,(
% 1.87/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.87/0.60  fof(f592,plain,(
% 1.87/0.60    sK4 != k1_funct_1(sK3,sK5(sK4,k1_xboole_0,sK3))),
% 1.87/0.60    inference(subsumption_resolution,[],[f589,f449])).
% 1.87/0.60  fof(f449,plain,(
% 1.87/0.60    ( ! [X0] : (r2_hidden(sK5(sK4,k1_xboole_0,sK3),X0)) )),
% 1.87/0.60    inference(resolution,[],[f343,f67])).
% 1.87/0.60  fof(f343,plain,(
% 1.87/0.60    ( ! [X13] : (r2_hidden(sK5(sK4,X13,sK3),X13)) )),
% 1.87/0.60    inference(resolution,[],[f209,f63])).
% 1.87/0.60  fof(f209,plain,(
% 1.87/0.60    ( ! [X6,X5] : (~v1_relat_1(X6) | r2_hidden(sK5(sK4,X5,X6),X5)) )),
% 1.87/0.60    inference(resolution,[],[f190,f40])).
% 1.87/0.60  fof(f589,plain,(
% 1.87/0.60    ~r2_hidden(sK5(sK4,k1_xboole_0,sK3),sK0) | sK4 != k1_funct_1(sK3,sK5(sK4,k1_xboole_0,sK3))),
% 1.87/0.60    inference(resolution,[],[f449,f28])).
% 1.87/0.60  % SZS output end Proof for theBenchmark
% 1.87/0.60  % (13963)------------------------------
% 1.87/0.60  % (13963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (13963)Termination reason: Refutation
% 1.87/0.60  
% 1.87/0.60  % (13963)Memory used [KB]: 2430
% 1.87/0.60  % (13963)Time elapsed: 0.151 s
% 1.87/0.60  % (13963)------------------------------
% 1.87/0.60  % (13963)------------------------------
% 1.87/0.60  % (13945)Success in time 0.234 s
%------------------------------------------------------------------------------
