%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 (1695 expanded)
%              Number of leaves         :   10 ( 314 expanded)
%              Depth                    :   35
%              Number of atoms          :  349 (9868 expanded)
%              Number of equality atoms :  129 (2420 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f289,f239])).

fof(f239,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f175,f229])).

fof(f229,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f228,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f228,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(resolution,[],[f181,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k1_xboole_0),sK3)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f180,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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

fof(f180,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,k1_xboole_0))
      | ~ r2_hidden(sK5(X0,k1_xboole_0),sK3) ) ),
    inference(forward_demodulation,[],[f179,f153])).

fof(f153,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f134,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f134,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f128])).

fof(f128,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f125,f35])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(resolution,[],[f124,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f123,f99])).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f95,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f34,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | sK0 != k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | ~ v1_relat_1(sK2)
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f120,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3)
      | sK2 = sK3
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f38,f80])).

fof(f80,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f78,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f77,f49])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f30,f55])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(sK3,sK2),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK4(sK3,sK2),sK0) ) ),
    inference(superposition,[],[f115,f28])).

fof(f28,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f114,f99])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f113,f80])).

fof(f113,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_relat_1(sK3) != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f110,f33])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f108,f48])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0 ) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k1_xboole_0),sK3)
      | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f161,f58])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,k1_xboole_0)),sK3)
      | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f73,f153])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK3) ) ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f175,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f155,f58])).

fof(f155,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f153])).

fof(f289,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f288,f58])).

fof(f288,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f277,f66])).

fof(f277,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f238,f265])).

fof(f265,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f264,f37])).

fof(f264,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(resolution,[],[f184,f42])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k1_xboole_0),sK2)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f183,f58])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,k1_xboole_0)),sK2)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f182,f153])).

fof(f182,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2) ) ),
    inference(forward_demodulation,[],[f162,f58])).

fof(f162,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,k1_xboole_0))
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2) ) ),
    inference(backward_demodulation,[],[f74,f153])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2) ) ),
    inference(resolution,[],[f72,f43])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f35,f40])).

fof(f238,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f156,f229])).

fof(f156,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f32,f153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3614)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.49  % (3614)Refutation not found, incomplete strategy% (3614)------------------------------
% 0.20/0.49  % (3614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3625)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (3614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3614)Memory used [KB]: 10746
% 0.20/0.50  % (3614)Time elapsed: 0.066 s
% 0.20/0.50  % (3614)------------------------------
% 0.20/0.50  % (3614)------------------------------
% 0.20/0.50  % (3625)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f289,f239])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    inference(backward_demodulation,[],[f175,f229])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    k1_xboole_0 = sK3),
% 0.20/0.50    inference(resolution,[],[f228,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    r1_tarski(sK3,k1_xboole_0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f226])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    r1_tarski(sK3,k1_xboole_0) | r1_tarski(sK3,k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f181,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK5(X0,k1_xboole_0),sK3) | r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f180,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(sK5(X0,k1_xboole_0),sK3)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f179,f153])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    k1_xboole_0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f152,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(resolution,[],[f134,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(superposition,[],[f32,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.51    inference(resolution,[],[f125,f35])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.20/0.51    inference(resolution,[],[f124,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f123,f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f97,f35])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(superposition,[],[f95,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f35])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(resolution,[],[f34,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | sK0 != k1_relat_1(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f122,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f121,f48])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f120,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(resolution,[],[f117,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f82,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(superposition,[],[f38,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f31])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(superposition,[],[f77,f49])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f31])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(resolution,[],[f30,f55])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(sK3,sK2),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | ~r2_hidden(sK4(sK3,sK2),sK0)) )),
% 0.20/0.51    inference(superposition,[],[f115,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f114,f99])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(superposition,[],[f113,f80])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X6,X4,X7,X5] : (k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.20/0.51    inference(resolution,[],[f110,f33])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.51    inference(resolution,[],[f108,f48])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.51    inference(resolution,[],[f67,f48])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) )),
% 0.20/0.51    inference(resolution,[],[f29,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK5(X0,k1_xboole_0),sK3) | r1_tarski(X0,k2_zfmisc_1(sK0,sK1))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f161,f58])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,k1_xboole_0)),sK3) | r1_tarski(X0,k2_zfmisc_1(sK0,sK1))) )),
% 0.20/0.51    inference(backward_demodulation,[],[f73,f153])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK3)) )),
% 0.20/0.51    inference(resolution,[],[f71,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) )),
% 0.20/0.51    inference(resolution,[],[f31,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f155,f58])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f31,f153])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f288,f58])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.51    inference(resolution,[],[f277,f66])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f238,f265])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    k1_xboole_0 = sK2),
% 0.20/0.51    inference(resolution,[],[f264,f37])).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f262])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f184,f42])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK5(X0,k1_xboole_0),sK2) | r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f183,f58])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,k1_xboole_0)),sK2) | r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f182,f153])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f162,f58])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2)) )),
% 0.20/0.51    inference(backward_demodulation,[],[f74,f153])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK5(X0,k2_zfmisc_1(sK0,sK1)),sK2)) )),
% 0.20/0.51    inference(resolution,[],[f72,f43])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.51    inference(resolution,[],[f35,f40])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f156,f229])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.20/0.51    inference(backward_demodulation,[],[f32,f153])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3625)------------------------------
% 0.20/0.51  % (3625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3625)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3625)Memory used [KB]: 1791
% 0.20/0.51  % (3625)Time elapsed: 0.071 s
% 0.20/0.51  % (3625)------------------------------
% 0.20/0.51  % (3625)------------------------------
% 0.20/0.51  % (3599)Success in time 0.151 s
%------------------------------------------------------------------------------
