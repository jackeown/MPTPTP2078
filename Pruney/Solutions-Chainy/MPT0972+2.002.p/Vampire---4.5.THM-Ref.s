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
% DateTime   : Thu Dec  3 13:01:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 690 expanded)
%              Number of leaves         :   11 ( 127 expanded)
%              Depth                    :   26
%              Number of atoms          :  309 (3938 expanded)
%              Number of equality atoms :  136 ( 951 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f314,f83])).

fof(f83,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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

fof(f314,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f267,f305])).

fof(f305,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f290,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f290,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f238,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f238,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f223,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f223,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f35,f218])).

fof(f218,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f203,f85])).

fof(f85,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f64,f35])).

fof(f203,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f199])).

fof(f199,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f198,f172])).

fof(f172,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f171,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f170,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
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

fof(f170,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f163,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f117,f92])).

fof(f92,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f117,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
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

fof(f163,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | k1_xboole_0 = sK1
      | k1_funct_1(sK2,sK4(sK3,X0)) = k1_funct_1(sK3,sK4(sK3,X0)) ) ),
    inference(resolution,[],[f154,f28])).

fof(f28,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f154,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f153,f73])).

fof(f73,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f153,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f147,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f40,f118])).

fof(f118,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f116,f91])).

fof(f91,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f31])).

fof(f116,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f111,f30])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f52,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f198,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f197,f33])).

fof(f197,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f196,f74])).

fof(f196,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f186,f120])).

fof(f186,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f185,f73])).

fof(f185,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f179,f29])).

fof(f179,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f41,f118])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f267,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f221,f262])).

fof(f262,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f247,f38])).

fof(f247,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f237,f70])).

fof(f237,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f220,f56])).

fof(f220,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f218])).

fof(f221,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f32,f218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:02:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (9188)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.47  % (9196)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.47  % (9196)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f314,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.49    inference(resolution,[],[f64,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.49    inference(equality_resolution,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f267,f305])).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    k1_xboole_0 = sK2),
% 0.20/0.49    inference(resolution,[],[f290,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    v1_xboole_0(sK2)),
% 0.20/0.49    inference(resolution,[],[f238,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f39,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(forward_demodulation,[],[f223,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f35,f218])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f203,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.49    inference(resolution,[],[f64,f35])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(superposition,[],[f32,f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f198,f172])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | k1_xboole_0 = sK1 | sK2 = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f171,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f45,f35])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))),
% 0.20/0.49    inference(subsumption_resolution,[],[f170,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(superposition,[],[f163,f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(superposition,[],[f117,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f46,f35])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f112,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f52,f35])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,X0)) = k1_funct_1(sK3,sK4(sK3,X0))) )),
% 0.20/0.49    inference(resolution,[],[f154,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f153,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    v1_relat_1(sK3)),
% 0.20/0.49    inference(resolution,[],[f45,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f147,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_funct_1(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(superposition,[],[f40,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(superposition,[],[f116,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.49    inference(resolution,[],[f46,f31])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f52,f31])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f33])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(subsumption_resolution,[],[f196,f74])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK3,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.20/0.49    inference(superposition,[],[f186,f120])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f185,f73])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f179,f29])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.20/0.49    inference(superposition,[],[f41,f118])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f221,f262])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    k1_xboole_0 = sK3),
% 0.20/0.49    inference(resolution,[],[f247,f38])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    v1_xboole_0(sK3)),
% 0.20/0.49    inference(resolution,[],[f237,f70])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(forward_demodulation,[],[f220,f56])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f31,f218])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f32,f218])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9196)------------------------------
% 0.20/0.49  % (9196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9196)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9196)Memory used [KB]: 1791
% 0.20/0.49  % (9196)Time elapsed: 0.075 s
% 0.20/0.49  % (9196)------------------------------
% 0.20/0.49  % (9196)------------------------------
% 0.20/0.49  % (9181)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (9176)Success in time 0.14 s
%------------------------------------------------------------------------------
