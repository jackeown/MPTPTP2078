%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 (31452 expanded)
%              Number of leaves         :    9 (5802 expanded)
%              Depth                    :   40
%              Number of atoms          :  345 (181395 expanded)
%              Number of equality atoms :  158 (43214 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(subsumption_resolution,[],[f462,f360])).

fof(f360,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f240,f347])).

fof(f347,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f346,f301])).

fof(f301,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f232,f262])).

fof(f262,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f260,f226])).

fof(f226,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f39,f224])).

fof(f224,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f200,f100])).

fof(f100,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f43,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(f200,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f40,f193])).

fof(f193,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f192,f127])).

fof(f127,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f97,f85])).

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f192,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f190,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f87,f83])).

fof(f83,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f38,f55])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f39,f63])).

fof(f190,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f126,f174])).

fof(f174,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f155,f36])).

fof(f36,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( m1_subset_1(sK4(sK3,sK2),sK0)
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f153,f152])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f137,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f137,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f136,f127])).

fof(f136,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f114,f120])).

fof(f114,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f113,f86])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f39,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f113,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f111,f96])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f64])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3))
      | sK3 = X0 ) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f153,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | m1_subset_1(sK4(sK3,sK2),sK0) ),
    inference(resolution,[],[f137,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f126,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f125,f86])).

fof(f125,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f123,f96])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f79,f41])).

fof(f79,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X1) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1 ) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f260,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f225,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f225,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f224])).

fof(f232,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f90,f224])).

fof(f90,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f39,f77])).

fof(f346,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f300,f266])).

fof(f266,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f264,f229])).

fof(f229,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f43,f224])).

fof(f264,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f228,f72])).

fof(f228,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f42,f224])).

fof(f300,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f227,f262])).

fof(f227,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f40,f224])).

fof(f240,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f100,f224])).

fof(f462,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f351,f451])).

fof(f451,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f448,f65])).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f448,plain,
    ( sK2 = sK3
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f399,f62])).

fof(f399,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f385,f392])).

fof(f392,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f359,f391])).

fof(f391,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f388,f353])).

fof(f353,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f229,f347])).

fof(f388,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f352,f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f352,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f228,f347])).

fof(f359,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f238,f347])).

fof(f238,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f97,f224])).

fof(f385,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f378,f375])).

fof(f375,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f354,f374])).

fof(f374,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f371,f350])).

fof(f350,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f226,f347])).

fof(f371,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f349,f70])).

fof(f349,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f225,f347])).

fof(f354,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f230,f347])).

fof(f230,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f87,f224])).

fof(f378,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f114,f375])).

fof(f351,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f227,f347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (2689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (2694)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (2696)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (2697)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (2706)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (2693)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (2709)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (2707)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (2704)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (2705)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (2701)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (2688)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (2686)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (2687)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2695)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (2691)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (2692)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (2686)Refutation not found, incomplete strategy% (2686)------------------------------
% 0.20/0.53  % (2686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2686)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2686)Memory used [KB]: 10746
% 0.20/0.53  % (2686)Time elapsed: 0.113 s
% 0.20/0.53  % (2686)------------------------------
% 0.20/0.53  % (2686)------------------------------
% 0.20/0.53  % (2693)Refutation not found, incomplete strategy% (2693)------------------------------
% 0.20/0.53  % (2693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2693)Memory used [KB]: 1791
% 0.20/0.53  % (2693)Time elapsed: 0.076 s
% 0.20/0.53  % (2693)------------------------------
% 0.20/0.53  % (2693)------------------------------
% 0.20/0.53  % (2710)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (2708)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (2711)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (2690)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (2703)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (2699)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (2702)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (2698)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.56  % (2691)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f472,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(subsumption_resolution,[],[f462,f360])).
% 0.20/0.56  fof(f360,plain,(
% 0.20/0.56    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f240,f347])).
% 0.20/0.56  fof(f347,plain,(
% 0.20/0.56    k1_xboole_0 = sK0),
% 0.20/0.56    inference(subsumption_resolution,[],[f346,f301])).
% 0.20/0.56  fof(f301,plain,(
% 0.20/0.56    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.56    inference(superposition,[],[f232,f262])).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(subsumption_resolution,[],[f260,f226])).
% 0.20/0.56  fof(f226,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.56    inference(backward_demodulation,[],[f39,f224])).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f200,f100])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.56    inference(resolution,[],[f43,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.56    inference(equality_resolution,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.56    inference(negated_conjecture,[],[f16])).
% 0.20/0.56  fof(f16,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f40,f193])).
% 0.20/0.56  fof(f193,plain,(
% 0.20/0.56    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f192,f127])).
% 0.20/0.56  fof(f127,plain,(
% 0.20/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f97,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f84,f43])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(resolution,[],[f42,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.56    inference(resolution,[],[f43,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f191])).
% 0.20/0.56  fof(f191,plain,(
% 0.20/0.56    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f190,f120])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f87,f83])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f82,f39])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(resolution,[],[f38,f55])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.56    inference(resolution,[],[f39,f63])).
% 0.20/0.56  fof(f190,plain,(
% 0.20/0.56    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f189])).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.56  fof(f188,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f126,f174])).
% 0.20/0.56  fof(f174,plain,(
% 0.20/0.56    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(resolution,[],[f155,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    m1_subset_1(sK4(sK3,sK2),sK0) | k1_xboole_0 = sK1 | sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f153,f152])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    ~v1_xboole_0(sK0) | k1_xboole_0 = sK1 | sK2 = sK3),
% 0.20/0.56    inference(resolution,[],[f137,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f136,f127])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    sK0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(superposition,[],[f114,f120])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f113,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    v1_relat_1(sK3)),
% 0.20/0.56    inference(resolution,[],[f39,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f111,f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    v1_relat_1(sK2)),
% 0.20/0.56    inference(resolution,[],[f43,f64])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.20/0.56    inference(resolution,[],[f78,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    v1_funct_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3)) | sK3 = X0) )),
% 0.20/0.56    inference(resolution,[],[f37,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    v1_funct_1(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    sK2 = sK3 | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | m1_subset_1(sK4(sK3,sK2),sK0)),
% 0.20/0.56    inference(resolution,[],[f137,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f125,f86])).
% 0.20/0.56  fof(f125,plain,(
% 0.20/0.56    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f123,f96])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.20/0.56    inference(resolution,[],[f79,f41])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3) | k1_relat_1(X1) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1) )),
% 0.20/0.56    inference(resolution,[],[f37,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f260,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.56    inference(resolution,[],[f225,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.56    inference(equality_resolution,[],[f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f225,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f38,f224])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    r2_relset_1(sK0,k1_xboole_0,sK3,sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f90,f224])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.20/0.56    inference(resolution,[],[f39,f77])).
% 0.20/0.56  fof(f346,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f345])).
% 0.20/0.56  fof(f345,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(superposition,[],[f300,f266])).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(subsumption_resolution,[],[f264,f229])).
% 0.20/0.56  fof(f229,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.56    inference(backward_demodulation,[],[f43,f224])).
% 0.20/0.56  fof(f264,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.56    inference(resolution,[],[f228,f72])).
% 0.20/0.56  fof(f228,plain,(
% 0.20/0.56    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f42,f224])).
% 0.20/0.56  fof(f300,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.56    inference(superposition,[],[f227,f262])).
% 0.20/0.56  fof(f227,plain,(
% 0.20/0.56    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f40,f224])).
% 0.20/0.56  fof(f240,plain,(
% 0.20/0.56    r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f100,f224])).
% 0.20/0.56  fof(f462,plain,(
% 0.20/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f351,f451])).
% 0.20/0.56  fof(f451,plain,(
% 0.20/0.56    sK2 = sK3),
% 0.20/0.56    inference(subsumption_resolution,[],[f448,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f448,plain,(
% 0.20/0.56    sK2 = sK3 | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(resolution,[],[f399,f62])).
% 0.20/0.56  fof(f399,plain,(
% 0.20/0.56    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f398])).
% 0.20/0.56  fof(f398,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 0.20/0.56    inference(backward_demodulation,[],[f385,f392])).
% 0.20/0.56  fof(f392,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f359,f391])).
% 0.20/0.56  fof(f391,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f388,f353])).
% 0.20/0.56  fof(f353,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.56    inference(backward_demodulation,[],[f229,f347])).
% 0.20/0.56  fof(f388,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.56    inference(resolution,[],[f352,f70])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.56    inference(equality_resolution,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f352,plain,(
% 0.20/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f228,f347])).
% 0.20/0.56  fof(f359,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f238,f347])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f97,f224])).
% 0.20/0.56  fof(f385,plain,(
% 0.20/0.56    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2) | sK2 = sK3),
% 0.20/0.56    inference(forward_demodulation,[],[f378,f375])).
% 0.20/0.56  fof(f375,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f354,f374])).
% 0.20/0.56  fof(f374,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.56    inference(subsumption_resolution,[],[f371,f350])).
% 0.20/0.56  fof(f350,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.56    inference(backward_demodulation,[],[f226,f347])).
% 0.20/0.56  fof(f371,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.56    inference(resolution,[],[f349,f70])).
% 0.20/0.56  fof(f349,plain,(
% 0.20/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f225,f347])).
% 0.20/0.56  fof(f354,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f230,f347])).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f87,f224])).
% 0.20/0.56  fof(f378,plain,(
% 0.20/0.56    k1_xboole_0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.20/0.56    inference(backward_demodulation,[],[f114,f375])).
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f227,f347])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (2691)------------------------------
% 0.20/0.56  % (2691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2691)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (2691)Memory used [KB]: 6268
% 0.20/0.56  % (2691)Time elapsed: 0.147 s
% 0.20/0.56  % (2691)------------------------------
% 0.20/0.56  % (2691)------------------------------
% 0.20/0.56  % (2685)Success in time 0.203 s
%------------------------------------------------------------------------------
