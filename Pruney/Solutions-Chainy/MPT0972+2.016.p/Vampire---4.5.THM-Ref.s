%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:07 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  170 (57781 expanded)
%              Number of leaves         :    8 (10767 expanded)
%              Depth                    :   74
%              Number of atoms          :  692 (346403 expanded)
%              Number of equality atoms :  380 (91809 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f707,plain,(
    $false ),
    inference(subsumption_resolution,[],[f704,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f704,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f683,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f683,plain,(
    ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f421,f667])).

fof(f667,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f666,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f666,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f665,f39])).

fof(f665,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f664,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f664,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f663,f487])).

fof(f487,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f304,f416])).

fof(f416,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f411,f37])).

fof(f411,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f374,f73])).

fof(f374,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f34,f366])).

fof(f366,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f361,f37])).

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = sK3
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f358,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f358,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK3
      | sK2 = sK3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f349,f54])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | sK2 = sK3
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f348,f54])).

fof(f348,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f347,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f214,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f121,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 = sK3 ),
    inference(superposition,[],[f37,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f111,f37])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(resolution,[],[f110,f33])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f109,f90])).

fof(f90,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f88,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f85,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f36,f61])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | sK0 != k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | ~ v1_relat_1(sK2)
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f106,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | sK0 != k1_relat_1(sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
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
    inference(resolution,[],[f103,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f40,f83])).

fof(f83,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f81,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f80,f55])).

fof(f80,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f76,f33])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f61])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(sK3,sK2),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | sK2 = sK3 ) ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK4(sK3,sK2),sK0) ) ),
    inference(superposition,[],[f101,f30])).

fof(f30,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f100,f90])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f99,f83])).

fof(f99,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_relat_1(sK3) != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f96,f35])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0 ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f214,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f209,f67])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f209,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK3
    | sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f176,f55])).

fof(f176,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f175,f127])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(forward_demodulation,[],[f171,f67])).

fof(f171,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f144,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f144,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f36,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK0
    | sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f132,f126])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f118,f66])).

fof(f118,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 = sK3 ),
    inference(superposition,[],[f33,f114])).

fof(f132,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f130,f66])).

fof(f130,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | sK2 = sK3 ),
    inference(superposition,[],[f32,f114])).

fof(f347,plain,
    ( k1_xboole_0 = sK3
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f343,f35])).

fof(f343,plain,
    ( k1_xboole_0 = sK3
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( k1_xboole_0 = sK3
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK2 = sK3
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(resolution,[],[f336,f207])).

fof(f207,plain,(
    ! [X8] :
      ( r2_hidden(sK4(sK3,X8),k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | ~ v1_relat_1(sK3)
      | sK3 = X8
      | k1_xboole_0 = sK3
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f204,f31])).

fof(f204,plain,(
    ! [X8] :
      ( r2_hidden(sK4(sK3,X8),k1_xboole_0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | ~ v1_relat_1(sK3)
      | sK3 = X8
      | k1_xboole_0 = sK3
      | sK2 = sK3 ) ),
    inference(superposition,[],[f40,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f196,f126])).

fof(f196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f191,f67])).

fof(f191,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | sK2 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f170,f55])).

fof(f170,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f169,f126])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(forward_demodulation,[],[f165,f67])).

fof(f165,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f141,f68])).

fof(f141,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f32,f140])).

fof(f336,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = sK3
    | sK2 = sK3
    | sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f327,f140])).

fof(f327,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | k1_xboole_0 = sK3
    | sK2 = sK3 ),
    inference(resolution,[],[f322,f37])).

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = sK3
      | k1_xboole_0 = sK3
      | ~ r2_hidden(sK4(sK3,sK2),sK0) ) ),
    inference(resolution,[],[f321,f33])).

fof(f321,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = sK3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(sK4(sK3,sK2),sK0) ) ),
    inference(trivial_inequality_removal,[],[f320])).

fof(f320,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(sK4(sK3,sK2),sK0) ) ),
    inference(superposition,[],[f319,f30])).

fof(f319,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f205,f215])).

fof(f205,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_xboole_0 != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_xboole_0 != k1_relat_1(sK2)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_xboole_0 = sK3
      | sK2 = sK3 ) ),
    inference(superposition,[],[f99,f197])).

fof(f34,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f304,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f303,f127])).

fof(f303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f298,f67])).

fof(f298,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f265,f55])).

fof(f265,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f264,f127])).

fof(f264,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(forward_demodulation,[],[f260,f67])).

fof(f260,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f234,f68])).

fof(f234,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f36,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f135,f127])).

fof(f135,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f133,f66])).

fof(f133,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f120,f70])).

fof(f120,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | sK2 = sK3 ),
    inference(superposition,[],[f36,f114])).

fof(f663,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f662,f54])).

fof(f662,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(sK2)
      | k1_xboole_0 != k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f661,f35])).

fof(f661,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 != k1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f659])).

fof(f659,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 != k1_relat_1(sK2) ) ),
    inference(resolution,[],[f657,f543])).

fof(f543,plain,(
    ! [X8] :
      ( r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0)
      | k1_xboole_0 = X8
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = X8
      | r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | k1_xboole_0 = sK2 ) ),
    inference(forward_demodulation,[],[f541,f416])).

fof(f541,plain,(
    ! [X8] :
      ( k1_xboole_0 = X8
      | r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | k1_xboole_0 = sK2
      | sK2 = sK3 ) ),
    inference(forward_demodulation,[],[f540,f416])).

fof(f540,plain,(
    ! [X8] :
      ( r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | sK3 = X8
      | k1_xboole_0 = sK2
      | sK2 = sK3 ) ),
    inference(forward_demodulation,[],[f470,f416])).

fof(f470,plain,(
    ! [X8] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK4(sK3,X8),k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | sK3 = X8
      | k1_xboole_0 = sK2
      | sK2 = sK3 ) ),
    inference(backward_demodulation,[],[f296,f416])).

fof(f296,plain,(
    ! [X8] :
      ( r2_hidden(sK4(sK3,X8),k1_xboole_0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | ~ v1_relat_1(sK3)
      | sK3 = X8
      | k1_xboole_0 = sK2
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f293,f31])).

fof(f293,plain,(
    ! [X8] :
      ( r2_hidden(sK4(sK3,X8),k1_xboole_0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 != k1_relat_1(X8)
      | ~ v1_relat_1(sK3)
      | sK3 = X8
      | k1_xboole_0 = sK2
      | sK2 = sK3 ) ),
    inference(superposition,[],[f40,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f285,f126])).

fof(f285,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f280,f67])).

fof(f280,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | sK2 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f259,f55])).

fof(f259,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f258,f126])).

fof(f258,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | sK2 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    inference(forward_demodulation,[],[f254,f67])).

fof(f254,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(resolution,[],[f231,f68])).

fof(f231,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f32,f230])).

fof(f657,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(duplicate_literal_removal,[],[f656])).

fof(f656,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f653,f499])).

fof(f499,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f230,f416])).

fof(f653,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_xboole_0,sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f652,f539])).

fof(f539,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f488,f416])).

fof(f488,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f286,f416])).

fof(f652,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK4(k1_xboole_0,sK2),sK0) ) ),
    inference(duplicate_literal_removal,[],[f650])).

fof(f650,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK4(k1_xboole_0,sK2),sK0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f649,f487])).

fof(f649,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK4(k1_xboole_0,sK2),sK0) ) ),
    inference(trivial_inequality_removal,[],[f648])).

fof(f648,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2))
      | k1_xboole_0 = sK2
      | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK4(k1_xboole_0,sK2),sK0) ) ),
    inference(superposition,[],[f516,f417])).

fof(f417,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f30,f416])).

fof(f516,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2))
      | k1_xboole_0 = sK2
      | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(subsumption_resolution,[],[f515,f39])).

fof(f515,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = sK2
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2))
      | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(forward_demodulation,[],[f514,f416])).

fof(f514,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_xboole_0 = sK2
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2))
      | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(forward_demodulation,[],[f513,f416])).

fof(f513,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2))
      | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(forward_demodulation,[],[f429,f416])).

fof(f429,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
      | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
      | sK2 = sK3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(backward_demodulation,[],[f99,f416])).

fof(f421,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f34,f416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n014.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 10:09:52 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.35  % (7711)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.11/0.35  % (7701)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.11/0.36  % (7718)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.11/0.36  % (7700)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.11/0.37  % (7712)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.37  % (7703)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.11/0.38  % (7706)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.11/0.38  % (7723)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.11/0.39  % (7704)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.11/0.39  % (7721)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.11/0.39  % (7722)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.11/0.39  % (7715)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.11/0.39  % (7724)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.11/0.39  % (7708)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.11/0.39  % (7705)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.11/0.39  % (7702)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.11/0.39  % (7708)Refutation not found, incomplete strategy% (7708)------------------------------
% 0.11/0.39  % (7708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (7708)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (7708)Memory used [KB]: 10746
% 0.11/0.39  % (7708)Time elapsed: 0.086 s
% 0.11/0.39  % (7708)------------------------------
% 0.11/0.39  % (7708)------------------------------
% 0.11/0.40  % (7717)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.11/0.40  % (7702)Refutation not found, incomplete strategy% (7702)------------------------------
% 0.11/0.40  % (7702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (7702)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (7702)Memory used [KB]: 10746
% 0.11/0.40  % (7702)Time elapsed: 0.093 s
% 0.11/0.40  % (7702)------------------------------
% 0.11/0.40  % (7702)------------------------------
% 0.11/0.40  % (7707)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.11/0.40  % (7726)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.11/0.40  % (7725)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.11/0.40  % (7714)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.11/0.40  % (7728)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.11/0.41  % (7727)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.11/0.41  % (7716)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.11/0.41  % (7713)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.11/0.41  % (7722)Refutation not found, incomplete strategy% (7722)------------------------------
% 0.11/0.41  % (7722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.41  % (7709)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.11/0.41  % (7720)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.11/0.41  % (7719)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.11/0.42  % (7710)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.11/0.42  % (7710)Refutation not found, incomplete strategy% (7710)------------------------------
% 0.11/0.42  % (7710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.42  % (7710)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.42  
% 0.11/0.42  % (7710)Memory used [KB]: 10746
% 0.11/0.42  % (7710)Time elapsed: 0.116 s
% 0.11/0.42  % (7710)------------------------------
% 0.11/0.42  % (7710)------------------------------
% 0.11/0.42  % (7729)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.11/0.42  % (7722)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.42  
% 0.11/0.42  % (7722)Memory used [KB]: 10874
% 0.11/0.42  % (7722)Time elapsed: 0.090 s
% 0.11/0.42  % (7722)------------------------------
% 0.11/0.42  % (7722)------------------------------
% 0.11/0.43  % (7721)Refutation found. Thanks to Tanya!
% 0.11/0.43  % SZS status Theorem for theBenchmark
% 0.11/0.43  % SZS output start Proof for theBenchmark
% 0.11/0.43  fof(f707,plain,(
% 0.11/0.43    $false),
% 0.11/0.43    inference(subsumption_resolution,[],[f704,f39])).
% 0.11/0.43  fof(f39,plain,(
% 0.11/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.11/0.43    inference(cnf_transformation,[],[f6])).
% 0.11/0.43  fof(f6,axiom,(
% 0.11/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.11/0.43  fof(f704,plain,(
% 0.11/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f683,f73])).
% 0.11/0.43  fof(f73,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (r2_relset_1(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.11/0.43    inference(condensation,[],[f63])).
% 0.11/0.43  fof(f63,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f29])).
% 0.11/0.43  fof(f29,plain,(
% 0.11/0.43    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(flattening,[],[f28])).
% 0.11/0.43  fof(f28,plain,(
% 0.11/0.43    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.11/0.43    inference(ennf_transformation,[],[f12])).
% 0.11/0.43  fof(f12,axiom,(
% 0.11/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.11/0.43  fof(f683,plain,(
% 0.11/0.43    ~r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)),
% 0.11/0.43    inference(backward_demodulation,[],[f421,f667])).
% 0.11/0.43  fof(f667,plain,(
% 0.11/0.43    k1_xboole_0 = sK2),
% 0.11/0.43    inference(resolution,[],[f666,f37])).
% 0.11/0.43  fof(f37,plain,(
% 0.11/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f17,plain,(
% 0.11/0.43    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.11/0.43    inference(flattening,[],[f16])).
% 0.11/0.43  fof(f16,plain,(
% 0.11/0.43    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.11/0.43    inference(ennf_transformation,[],[f15])).
% 0.11/0.43  fof(f15,negated_conjecture,(
% 0.11/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.11/0.43    inference(negated_conjecture,[],[f14])).
% 0.11/0.43  fof(f14,conjecture,(
% 0.11/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.11/0.43  fof(f666,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f665,f39])).
% 0.11/0.43  fof(f665,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.11/0.43    inference(resolution,[],[f664,f54])).
% 0.11/0.43  fof(f54,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.43    inference(cnf_transformation,[],[f22])).
% 0.11/0.43  fof(f22,plain,(
% 0.11/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(ennf_transformation,[],[f9])).
% 0.11/0.43  fof(f9,axiom,(
% 0.11/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.11/0.43  fof(f664,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f663,f487])).
% 0.11/0.43  fof(f487,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f471])).
% 0.11/0.43  fof(f471,plain,(
% 0.11/0.43    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.11/0.43    inference(backward_demodulation,[],[f304,f416])).
% 0.11/0.43  fof(f416,plain,(
% 0.11/0.43    k1_xboole_0 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f411,f37])).
% 0.11/0.43  fof(f411,plain,(
% 0.11/0.43    k1_xboole_0 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f374,f73])).
% 0.11/0.43  fof(f374,plain,(
% 0.11/0.43    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK3),
% 0.11/0.43    inference(superposition,[],[f34,f366])).
% 0.11/0.43  fof(f366,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(resolution,[],[f361,f37])).
% 0.11/0.43  fof(f361,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3 | k1_xboole_0 = sK3) )),
% 0.11/0.43    inference(resolution,[],[f358,f33])).
% 0.11/0.43  fof(f33,plain,(
% 0.11/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f358,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK3 | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.11/0.43    inference(resolution,[],[f349,f54])).
% 0.11/0.43  fof(f349,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.43    inference(resolution,[],[f348,f54])).
% 0.11/0.43  fof(f348,plain,(
% 0.11/0.43    ~v1_relat_1(sK3) | sK2 = sK3 | ~v1_relat_1(sK2) | k1_xboole_0 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f347,f215])).
% 0.11/0.43  fof(f215,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f214,f127])).
% 0.11/0.43  fof(f127,plain,(
% 0.11/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f121,f66])).
% 0.11/0.43  fof(f66,plain,(
% 0.11/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.11/0.43    inference(equality_resolution,[],[f53])).
% 0.11/0.43  fof(f53,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f5])).
% 0.11/0.43  fof(f5,axiom,(
% 0.11/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.11/0.43  fof(f121,plain,(
% 0.11/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | sK2 = sK3),
% 0.11/0.43    inference(superposition,[],[f37,f114])).
% 0.11/0.43  fof(f114,plain,(
% 0.11/0.43    k1_xboole_0 = sK1 | sK2 = sK3),
% 0.11/0.43    inference(resolution,[],[f111,f37])).
% 0.11/0.43  fof(f111,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.11/0.43    inference(resolution,[],[f110,f33])).
% 0.11/0.43  fof(f110,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f109,f90])).
% 0.11/0.43  fof(f90,plain,(
% 0.11/0.43    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.11/0.43    inference(subsumption_resolution,[],[f88,f37])).
% 0.11/0.43  fof(f88,plain,(
% 0.11/0.43    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f85,f55])).
% 0.11/0.43  fof(f55,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.43    inference(cnf_transformation,[],[f23])).
% 0.11/0.43  fof(f23,plain,(
% 0.11/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(ennf_transformation,[],[f11])).
% 0.11/0.43  fof(f11,axiom,(
% 0.11/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.11/0.43  fof(f85,plain,(
% 0.11/0.43    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.11/0.43    inference(subsumption_resolution,[],[f77,f37])).
% 0.11/0.43  fof(f77,plain,(
% 0.11/0.43    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f36,f61])).
% 0.11/0.43  fof(f61,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.43    inference(cnf_transformation,[],[f25])).
% 0.11/0.43  fof(f25,plain,(
% 0.11/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(flattening,[],[f24])).
% 0.11/0.43  fof(f24,plain,(
% 0.11/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(ennf_transformation,[],[f13])).
% 0.11/0.43  fof(f13,axiom,(
% 0.11/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.11/0.43  fof(f36,plain,(
% 0.11/0.43    v1_funct_2(sK2,sK0,sK1)),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f109,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | sK0 != k1_relat_1(sK2)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f108,f54])).
% 0.11/0.43  fof(f108,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f107,f54])).
% 0.11/0.43  fof(f107,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f106,f35])).
% 0.11/0.43  fof(f35,plain,(
% 0.11/0.43    v1_funct_1(sK2)),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f106,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f104])).
% 0.11/0.43  fof(f104,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_xboole_0 = sK1) )),
% 0.11/0.43    inference(resolution,[],[f103,f87])).
% 0.11/0.43  fof(f87,plain,(
% 0.11/0.43    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f86,f31])).
% 0.11/0.43  fof(f31,plain,(
% 0.11/0.43    v1_funct_1(sK3)),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f86,plain,(
% 0.11/0.43    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.11/0.43    inference(superposition,[],[f40,f83])).
% 0.11/0.43  fof(f83,plain,(
% 0.11/0.43    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.11/0.43    inference(subsumption_resolution,[],[f81,f33])).
% 0.11/0.43  fof(f81,plain,(
% 0.11/0.43    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f80,f55])).
% 0.11/0.43  fof(f80,plain,(
% 0.11/0.43    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.11/0.43    inference(subsumption_resolution,[],[f76,f33])).
% 0.11/0.43  fof(f76,plain,(
% 0.11/0.43    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f32,f61])).
% 0.11/0.43  fof(f32,plain,(
% 0.11/0.43    v1_funct_2(sK3,sK0,sK1)),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f40,plain,(
% 0.11/0.43    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.11/0.43    inference(cnf_transformation,[],[f19])).
% 0.11/0.43  fof(f19,plain,(
% 0.11/0.43    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.11/0.43    inference(flattening,[],[f18])).
% 0.11/0.43  fof(f18,plain,(
% 0.11/0.43    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.11/0.43    inference(ennf_transformation,[],[f8])).
% 0.11/0.43  fof(f8,axiom,(
% 0.11/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.11/0.43  fof(f103,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(sK3,sK2),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | sK2 = sK3) )),
% 0.11/0.43    inference(trivial_inequality_removal,[],[f102])).
% 0.11/0.43  fof(f102,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1 | ~r2_hidden(sK4(sK3,sK2),sK0)) )),
% 0.11/0.43    inference(superposition,[],[f101,f30])).
% 0.11/0.43  fof(f30,plain,(
% 0.11/0.43    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f101,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f100,f90])).
% 0.11/0.43  fof(f100,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK1) )),
% 0.11/0.43    inference(superposition,[],[f99,f83])).
% 0.11/0.43  fof(f99,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(resolution,[],[f96,f35])).
% 0.11/0.43  fof(f96,plain,(
% 0.11/0.43    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.11/0.43    inference(resolution,[],[f94,f54])).
% 0.11/0.43  fof(f94,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.11/0.43    inference(resolution,[],[f74,f54])).
% 0.11/0.43  fof(f74,plain,(
% 0.11/0.43    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) )),
% 0.11/0.43    inference(resolution,[],[f31,f41])).
% 0.11/0.43  fof(f41,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.11/0.43    inference(cnf_transformation,[],[f19])).
% 0.11/0.43  fof(f214,plain,(
% 0.11/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f209,f67])).
% 0.11/0.43  fof(f67,plain,(
% 0.11/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.11/0.43    inference(equality_resolution,[],[f52])).
% 0.11/0.43  fof(f52,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f5])).
% 0.11/0.43  fof(f209,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK3 | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f176,f55])).
% 0.11/0.43  fof(f176,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f175,f127])).
% 0.11/0.43  fof(f175,plain,(
% 0.11/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.11/0.43    inference(forward_demodulation,[],[f171,f67])).
% 0.11/0.43  fof(f171,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f144,f68])).
% 0.11/0.43  fof(f68,plain,(
% 0.11/0.43    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.11/0.43    inference(equality_resolution,[],[f59])).
% 0.11/0.43  fof(f59,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f25])).
% 0.11/0.43  fof(f144,plain,(
% 0.11/0.43    v1_funct_2(sK2,k1_xboole_0,sK1) | sK2 = sK3 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(superposition,[],[f36,f140])).
% 0.11/0.43  fof(f140,plain,(
% 0.11/0.43    k1_xboole_0 = sK0 | sK2 = sK3 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f132,f126])).
% 0.11/0.43  fof(f126,plain,(
% 0.11/0.43    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f118,f66])).
% 0.11/0.43  fof(f118,plain,(
% 0.11/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | sK2 = sK3),
% 0.11/0.43    inference(superposition,[],[f33,f114])).
% 0.11/0.43  fof(f132,plain,(
% 0.11/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f130,f66])).
% 0.11/0.43  fof(f130,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.11/0.43    inference(resolution,[],[f117,f70])).
% 0.11/0.43  fof(f70,plain,(
% 0.11/0.43    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.11/0.43    inference(equality_resolution,[],[f57])).
% 0.11/0.43  fof(f57,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f25])).
% 0.11/0.43  fof(f117,plain,(
% 0.11/0.43    v1_funct_2(sK3,sK0,k1_xboole_0) | sK2 = sK3),
% 0.11/0.43    inference(superposition,[],[f32,f114])).
% 0.11/0.43  fof(f347,plain,(
% 0.11/0.43    k1_xboole_0 = sK3 | sK2 = sK3 | ~v1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 0.11/0.43    inference(subsumption_resolution,[],[f343,f35])).
% 0.11/0.43  fof(f343,plain,(
% 0.11/0.43    k1_xboole_0 = sK3 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f341])).
% 0.11/0.43  fof(f341,plain,(
% 0.11/0.43    k1_xboole_0 = sK3 | sK2 = sK3 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(resolution,[],[f336,f207])).
% 0.11/0.43  fof(f207,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(sK3,X8),k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | ~v1_relat_1(sK3) | sK3 = X8 | k1_xboole_0 = sK3 | sK2 = sK3) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f204,f31])).
% 0.11/0.43  fof(f204,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(sK3,X8),k1_xboole_0) | ~v1_funct_1(sK3) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | ~v1_relat_1(sK3) | sK3 = X8 | k1_xboole_0 = sK3 | sK2 = sK3) )),
% 0.11/0.43    inference(superposition,[],[f40,f197])).
% 0.11/0.43  fof(f197,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f196,f126])).
% 0.11/0.43  fof(f196,plain,(
% 0.11/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f191,f67])).
% 0.11/0.43  fof(f191,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f170,f55])).
% 0.11/0.43  fof(f170,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f169,f126])).
% 0.11/0.43  fof(f169,plain,(
% 0.11/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.11/0.43    inference(forward_demodulation,[],[f165,f67])).
% 0.11/0.43  fof(f165,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f141,f68])).
% 0.11/0.43  fof(f141,plain,(
% 0.11/0.43    v1_funct_2(sK3,k1_xboole_0,sK1) | sK2 = sK3 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(superposition,[],[f32,f140])).
% 0.11/0.43  fof(f336,plain,(
% 0.11/0.43    ~r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f335])).
% 0.11/0.43  fof(f335,plain,(
% 0.11/0.43    ~r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 = sK3 | sK2 = sK3 | sK2 = sK3 | k1_xboole_0 = sK3),
% 0.11/0.43    inference(superposition,[],[f327,f140])).
% 0.11/0.43  fof(f327,plain,(
% 0.11/0.43    ~r2_hidden(sK4(sK3,sK2),sK0) | k1_xboole_0 = sK3 | sK2 = sK3),
% 0.11/0.43    inference(resolution,[],[f322,f37])).
% 0.11/0.43  fof(f322,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3 | k1_xboole_0 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0)) )),
% 0.11/0.43    inference(resolution,[],[f321,f33])).
% 0.11/0.43  fof(f321,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0)) )),
% 0.11/0.43    inference(trivial_inequality_removal,[],[f320])).
% 0.11/0.43  fof(f320,plain,(
% 0.11/0.43    ( ! [X2,X0,X3,X1] : (k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0)) )),
% 0.11/0.43    inference(superposition,[],[f319,f30])).
% 0.11/0.43  fof(f319,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_xboole_0 = sK3) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f205,f215])).
% 0.11/0.43  fof(f205,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_xboole_0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_xboole_0 = sK3) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f202])).
% 0.11/0.43  fof(f202,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_xboole_0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_xboole_0 = sK3 | sK2 = sK3) )),
% 0.11/0.43    inference(superposition,[],[f99,f197])).
% 0.11/0.43  fof(f34,plain,(
% 0.11/0.43    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.11/0.43    inference(cnf_transformation,[],[f17])).
% 0.11/0.43  fof(f304,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f303,f127])).
% 0.11/0.43  fof(f303,plain,(
% 0.11/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f298,f67])).
% 0.11/0.43  fof(f298,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f265,f55])).
% 0.11/0.43  fof(f265,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f264,f127])).
% 0.11/0.43  fof(f264,plain,(
% 0.11/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.11/0.43    inference(forward_demodulation,[],[f260,f67])).
% 0.11/0.43  fof(f260,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f234,f68])).
% 0.11/0.43  fof(f234,plain,(
% 0.11/0.43    v1_funct_2(sK2,k1_xboole_0,sK1) | sK2 = sK3 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(superposition,[],[f36,f230])).
% 0.11/0.43  fof(f230,plain,(
% 0.11/0.43    k1_xboole_0 = sK0 | sK2 = sK3 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(subsumption_resolution,[],[f135,f127])).
% 0.11/0.43  fof(f135,plain,(
% 0.11/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(forward_demodulation,[],[f133,f66])).
% 0.11/0.43  fof(f133,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.11/0.43    inference(resolution,[],[f120,f70])).
% 0.11/0.43  fof(f120,plain,(
% 0.11/0.43    v1_funct_2(sK2,sK0,k1_xboole_0) | sK2 = sK3),
% 0.11/0.43    inference(superposition,[],[f36,f114])).
% 0.11/0.43  fof(f663,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2 | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f662,f54])).
% 0.11/0.43  fof(f662,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f661,f35])).
% 0.11/0.43  fof(f661,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_xboole_0 != k1_relat_1(sK2)) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f659])).
% 0.11/0.43  fof(f659,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_xboole_0 != k1_relat_1(sK2)) )),
% 0.11/0.43    inference(resolution,[],[f657,f543])).
% 0.11/0.43  fof(f543,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0) | k1_xboole_0 = X8 | k1_xboole_0 = sK2 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8)) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f542])).
% 0.11/0.43  fof(f542,plain,(
% 0.11/0.43    ( ! [X8] : (k1_xboole_0 = sK2 | k1_xboole_0 = X8 | r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(forward_demodulation,[],[f541,f416])).
% 0.11/0.43  fof(f541,plain,(
% 0.11/0.43    ( ! [X8] : (k1_xboole_0 = X8 | r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | k1_xboole_0 = sK2 | sK2 = sK3) )),
% 0.11/0.43    inference(forward_demodulation,[],[f540,f416])).
% 0.11/0.43  fof(f540,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(k1_xboole_0,X8),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | sK3 = X8 | k1_xboole_0 = sK2 | sK2 = sK3) )),
% 0.11/0.43    inference(forward_demodulation,[],[f470,f416])).
% 0.11/0.43  fof(f470,plain,(
% 0.11/0.43    ( ! [X8] : (~v1_relat_1(k1_xboole_0) | r2_hidden(sK4(sK3,X8),k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | sK3 = X8 | k1_xboole_0 = sK2 | sK2 = sK3) )),
% 0.11/0.43    inference(backward_demodulation,[],[f296,f416])).
% 0.11/0.43  fof(f296,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(sK3,X8),k1_xboole_0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | ~v1_relat_1(sK3) | sK3 = X8 | k1_xboole_0 = sK2 | sK2 = sK3) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f293,f31])).
% 0.11/0.43  fof(f293,plain,(
% 0.11/0.43    ( ! [X8] : (r2_hidden(sK4(sK3,X8),k1_xboole_0) | ~v1_funct_1(sK3) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k1_xboole_0 != k1_relat_1(X8) | ~v1_relat_1(sK3) | sK3 = X8 | k1_xboole_0 = sK2 | sK2 = sK3) )),
% 0.11/0.43    inference(superposition,[],[f40,f286])).
% 0.11/0.43  fof(f286,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f285,f126])).
% 0.11/0.43  fof(f285,plain,(
% 0.11/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(forward_demodulation,[],[f280,f67])).
% 0.11/0.43  fof(f280,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(superposition,[],[f259,f55])).
% 0.11/0.43  fof(f259,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | k1_xboole_0 = sK2 | sK2 = sK3),
% 0.11/0.43    inference(subsumption_resolution,[],[f258,f126])).
% 0.11/0.43  fof(f258,plain,(
% 0.11/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | sK2 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.11/0.43    inference(forward_demodulation,[],[f254,f67])).
% 0.11/0.43  fof(f254,plain,(
% 0.11/0.43    sK2 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.11/0.43    inference(resolution,[],[f231,f68])).
% 0.11/0.43  fof(f231,plain,(
% 0.11/0.43    v1_funct_2(sK3,k1_xboole_0,sK1) | sK2 = sK3 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(superposition,[],[f32,f230])).
% 0.11/0.43  fof(f657,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f656])).
% 0.11/0.43  fof(f656,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(superposition,[],[f653,f499])).
% 0.11/0.43  fof(f499,plain,(
% 0.11/0.43    k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f458])).
% 0.11/0.43  fof(f458,plain,(
% 0.11/0.43    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.11/0.43    inference(backward_demodulation,[],[f230,f416])).
% 0.11/0.43  fof(f653,plain,(
% 0.11/0.43    ( ! [X0,X1] : (~r2_hidden(sK4(k1_xboole_0,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f652,f539])).
% 0.11/0.43  fof(f539,plain,(
% 0.11/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2),
% 0.11/0.43    inference(forward_demodulation,[],[f488,f416])).
% 0.11/0.43  fof(f488,plain,(
% 0.11/0.43    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK3)),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f469])).
% 0.11/0.43  fof(f469,plain,(
% 0.11/0.43    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.11/0.43    inference(backward_demodulation,[],[f286,f416])).
% 0.11/0.43  fof(f652,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK4(k1_xboole_0,sK2),sK0)) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f650])).
% 0.11/0.43  fof(f650,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK4(k1_xboole_0,sK2),sK0) | k1_xboole_0 = sK2) )),
% 0.11/0.43    inference(superposition,[],[f649,f487])).
% 0.11/0.43  fof(f649,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK4(k1_xboole_0,sK2),sK0)) )),
% 0.11/0.43    inference(trivial_inequality_removal,[],[f648])).
% 0.11/0.43  fof(f648,plain,(
% 0.11/0.43    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) | k1_xboole_0 = sK2 | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK4(k1_xboole_0,sK2),sK0)) )),
% 0.11/0.43    inference(superposition,[],[f516,f417])).
% 0.11/0.43  fof(f417,plain,(
% 0.11/0.43    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(k1_xboole_0,X4) | ~r2_hidden(X4,sK0)) )),
% 0.11/0.43    inference(backward_demodulation,[],[f30,f416])).
% 0.11/0.43  fof(f516,plain,(
% 0.11/0.43    ( ! [X6,X7] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2)) | k1_xboole_0 = sK2 | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f515,f39])).
% 0.11/0.43  fof(f515,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_xboole_0 = sK2 | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2)) | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(forward_demodulation,[],[f514,f416])).
% 0.11/0.43  fof(f514,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_xboole_0 = sK2 | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2)) | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(forward_demodulation,[],[f513,f416])).
% 0.11/0.43  fof(f513,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,sK2)) | k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(forward_demodulation,[],[f429,f416])).
% 0.11/0.43  fof(f429,plain,(
% 0.11/0.43    ( ! [X6,X4,X7,X5] : (k1_relat_1(sK2) != k1_relat_1(k1_xboole_0) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.11/0.43    inference(backward_demodulation,[],[f99,f416])).
% 0.11/0.43  fof(f421,plain,(
% 0.11/0.43    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0)),
% 0.11/0.43    inference(backward_demodulation,[],[f34,f416])).
% 0.11/0.43  % SZS output end Proof for theBenchmark
% 0.11/0.43  % (7721)------------------------------
% 0.11/0.43  % (7721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.43  % (7721)Termination reason: Refutation
% 0.11/0.43  
% 0.11/0.43  % (7721)Memory used [KB]: 1918
% 0.11/0.43  % (7721)Time elapsed: 0.119 s
% 0.11/0.43  % (7721)------------------------------
% 0.11/0.43  % (7721)------------------------------
% 0.11/0.43  % (7699)Success in time 0.155 s
%------------------------------------------------------------------------------
