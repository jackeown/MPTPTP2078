%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 740 expanded)
%              Number of leaves         :   12 ( 143 expanded)
%              Depth                    :   26
%              Number of atoms          :  323 (4052 expanded)
%              Number of equality atoms :  137 ( 965 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(subsumption_resolution,[],[f343,f95])).

fof(f95,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f343,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f292,f332])).

fof(f332,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f318,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f318,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f261,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f87,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f261,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f246,f58])).

fof(f246,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f241])).

fof(f241,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f223,f97])).

fof(f97,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f66,f36])).

fof(f223,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f219])).

fof(f219,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f218,f198])).

fof(f198,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f197,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f197,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f196,f80])).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f196,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f185,f132])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f129,f104])).

fof(f104,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f185,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f184,f79])).

fof(f79,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f184,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f178,f30])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f41,f130])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f128,f103])).

fof(f103,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f48,f32])).

fof(f128,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f54,f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f218,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f217,f80])).

fof(f217,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f216,f34])).

fof(f216,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(trivial_inequality_removal,[],[f215])).

fof(f215,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f175,f132])).

fof(f175,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | k1_xboole_0 = sK1
      | k1_funct_1(sK2,sK4(sK3,X0)) = k1_funct_1(sK3,sK4(sK3,X0)) ) ),
    inference(resolution,[],[f166,f29])).

fof(f29,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f166,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0),sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f165,f79])).

fof(f165,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f159,f30])).

fof(f159,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f40,f130])).

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

fof(f33,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f292,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f244,f285])).

fof(f285,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f271,f73])).

fof(f271,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f260,f88])).

fof(f260,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f243,f58])).

fof(f243,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f32,f241])).

fof(f244,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f33,f241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:18:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (30534)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.48  % (30542)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (30542)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f354,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f343,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f66,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.52    inference(equality_resolution,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.52  fof(f343,plain,(
% 0.22/0.52    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f292,f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(resolution,[],[f318,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f47,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    v1_xboole_0(sK2)),
% 0.22/0.52    inference(resolution,[],[f261,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f87,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f43,f37])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    inference(forward_demodulation,[],[f246,f58])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f36,f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f223,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.52    inference(resolution,[],[f66,f36])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f33,f219])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f198])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f197,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f196,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f75,f36])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f39,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f195])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f185,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f129,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f48,f36])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f124,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f54,f36])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f184,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f75,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(superposition,[],[f41,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f128,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f48,f32])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f54,f32])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f217,f80])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f216,f34])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f215])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f214])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f175,f132])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4(sK3,X0)) = k1_funct_1(sK3,sK4(sK3,X0))) )),
% 0.22/0.52    inference(resolution,[],[f166,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f79])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f159,f30])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(superposition,[],[f40,f130])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f292,plain,(
% 0.22/0.52    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f244,f285])).
% 0.22/0.52  fof(f285,plain,(
% 0.22/0.52    k1_xboole_0 = sK3),
% 0.22/0.52    inference(resolution,[],[f271,f73])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    v1_xboole_0(sK3)),
% 0.22/0.52    inference(resolution,[],[f260,f88])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    inference(forward_demodulation,[],[f243,f58])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f32,f241])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.22/0.52    inference(backward_demodulation,[],[f33,f241])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (30542)------------------------------
% 0.22/0.52  % (30542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30542)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (30542)Memory used [KB]: 1791
% 0.22/0.52  % (30542)Time elapsed: 0.089 s
% 0.22/0.52  % (30542)------------------------------
% 0.22/0.52  % (30542)------------------------------
% 0.22/0.52  % (30522)Success in time 0.157 s
%------------------------------------------------------------------------------
