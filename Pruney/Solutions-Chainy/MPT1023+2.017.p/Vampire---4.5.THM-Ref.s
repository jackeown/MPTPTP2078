%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:09 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  130 (57119 expanded)
%              Number of leaves         :    9 (10571 expanded)
%              Depth                    :   44
%              Number of atoms          :  378 (327477 expanded)
%              Number of equality atoms :  183 (78669 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(subsumption_resolution,[],[f389,f311])).

fof(f311,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f210,f303])).

fof(f303,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f302,f268])).

fof(f268,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f205,f245])).

fof(f245,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f244,f220])).

fof(f220,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f200,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f200,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f198])).

fof(f198,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f175,f86])).

fof(f86,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f35,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
                  ( m1_subset_1(X4,X0)
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
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f175,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f171])).

fof(f171,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f170,f96])).

fof(f96,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f84])).

fof(f84,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f74,f35])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f170,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f165,f94])).

fof(f94,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f73,f77])).

fof(f77,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f31,f56])).

fof(f73,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f72,f31])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f30,f49])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f165,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f112,f147])).

fof(f147,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f130,f28])).

fof(f28,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,
    ( m1_subset_1(sK4(sK3,sK2),sK0)
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f129,f128])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f123,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f123,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f122,f96])).

fof(f122,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f102,f94])).

fof(f102,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f101,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f31,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f99,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f35,f57])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3))
      | sK3 = X0 ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK0)
    | m1_subset_1(sK4(sK3,sK2),sK0) ),
    inference(resolution,[],[f123,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f112,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f111,f76])).

fof(f111,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X1) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1 ) ),
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
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f242,f60])).

fof(f242,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f199,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f199,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f198])).

fof(f205,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f79,f198])).

fof(f79,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f31,f67])).

fof(f302,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f267,f249])).

fof(f249,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f248,f221])).

fof(f221,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f203,f60])).

fof(f203,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f35,f198])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f246,f60])).

fof(f246,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f202,f64])).

fof(f202,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f34,f198])).

fof(f267,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f201,f245])).

fof(f201,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f32,f198])).

fof(f210,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f86,f198])).

fof(f389,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f306,f378])).

fof(f378,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f375,f344])).

fof(f344,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f322,f334])).

fof(f334,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f333,f221])).

fof(f333,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f332,f60])).

fof(f332,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f329,f310])).

fof(f310,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f209,f303])).

fof(f209,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f84,f198])).

fof(f329,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f307,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f307,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f202,f303])).

fof(f322,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f112,f317])).

fof(f317,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f316,f220])).

fof(f316,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f315,f60])).

fof(f315,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f312,f308])).

fof(f308,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f204,f303])).

fof(f204,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f77,f198])).

fof(f312,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f305,f62])).

fof(f305,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f199,f303])).

fof(f375,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f371,f304])).

fof(f304,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_xboole_0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(backward_demodulation,[],[f28,f303])).

fof(f371,plain,
    ( m1_subset_1(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f370,f369])).

fof(f369,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK2 = sK3 ),
    inference(resolution,[],[f342,f55])).

fof(f342,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f341])).

fof(f341,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f328,f334])).

fof(f328,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f320,f317])).

fof(f320,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f102,f317])).

fof(f370,plain,
    ( sK2 = sK3
    | v1_xboole_0(k1_xboole_0)
    | m1_subset_1(sK4(sK3,sK2),k1_xboole_0) ),
    inference(resolution,[],[f342,f52])).

fof(f306,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f201,f303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (2866)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (2875)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.50/0.56  % (2857)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.50/0.56  % (2859)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.50/0.57  % (2858)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.66/0.57  % (2867)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.66/0.58  % (2864)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.66/0.58  % (2855)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.58  % (2873)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.66/0.58  % (2874)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.66/0.58  % (2876)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.66/0.58  % (2856)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.66/0.59  % (2869)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.66/0.59  % (2868)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.66/0.59  % (2870)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.66/0.59  % (2872)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.66/0.59  % (2854)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.66/0.59  % (2859)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f399,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(subsumption_resolution,[],[f389,f311])).
% 1.66/0.59  fof(f311,plain,(
% 1.66/0.59    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.66/0.59    inference(backward_demodulation,[],[f210,f303])).
% 1.66/0.59  fof(f303,plain,(
% 1.66/0.59    k1_xboole_0 = sK0),
% 1.66/0.59    inference(subsumption_resolution,[],[f302,f268])).
% 1.66/0.59  fof(f268,plain,(
% 1.66/0.59    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.66/0.59    inference(superposition,[],[f205,f245])).
% 1.66/0.59  fof(f245,plain,(
% 1.66/0.59    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.66/0.59    inference(subsumption_resolution,[],[f244,f220])).
% 1.66/0.59  fof(f220,plain,(
% 1.66/0.59    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.66/0.59    inference(forward_demodulation,[],[f200,f60])).
% 1.66/0.59  fof(f60,plain,(
% 1.66/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.66/0.59    inference(equality_resolution,[],[f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.66/0.59  fof(f200,plain,(
% 1.66/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.66/0.59    inference(backward_demodulation,[],[f31,f198])).
% 1.66/0.59  fof(f198,plain,(
% 1.66/0.59    k1_xboole_0 = sK1),
% 1.66/0.59    inference(subsumption_resolution,[],[f175,f86])).
% 1.66/0.59  fof(f86,plain,(
% 1.66/0.59    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.66/0.59    inference(resolution,[],[f35,f67])).
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.66/0.59    inference(duplicate_literal_removal,[],[f59])).
% 1.66/0.59  fof(f59,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.66/0.59    inference(equality_resolution,[],[f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(flattening,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,plain,(
% 1.66/0.59    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.66/0.59    inference(flattening,[],[f15])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.66/0.59    inference(ennf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.66/0.59    inference(negated_conjecture,[],[f13])).
% 1.66/0.59  fof(f13,conjecture,(
% 1.66/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 1.66/0.59  fof(f175,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f32,f171])).
% 1.66/0.59  fof(f171,plain,(
% 1.66/0.59    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(subsumption_resolution,[],[f170,f96])).
% 1.66/0.59  fof(f96,plain,(
% 1.66/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f75,f84])).
% 1.66/0.59  fof(f84,plain,(
% 1.66/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.59    inference(resolution,[],[f35,f56])).
% 1.66/0.59  fof(f56,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.66/0.59  fof(f75,plain,(
% 1.66/0.59    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.66/0.59    inference(subsumption_resolution,[],[f74,f35])).
% 1.66/0.59  fof(f74,plain,(
% 1.66/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(resolution,[],[f34,f49])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(flattening,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f170,plain,(
% 1.66/0.59    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(duplicate_literal_removal,[],[f169])).
% 1.66/0.59  fof(f169,plain,(
% 1.66/0.59    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f165,f94])).
% 1.66/0.59  fof(f94,plain,(
% 1.66/0.59    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f73,f77])).
% 1.66/0.59  fof(f77,plain,(
% 1.66/0.59    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.66/0.59    inference(resolution,[],[f31,f56])).
% 1.66/0.59  fof(f73,plain,(
% 1.66/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.66/0.59    inference(subsumption_resolution,[],[f72,f31])).
% 1.66/0.59  fof(f72,plain,(
% 1.66/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(resolution,[],[f30,f49])).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f165,plain,(
% 1.66/0.59    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(trivial_inequality_removal,[],[f164])).
% 1.66/0.59  fof(f164,plain,(
% 1.66/0.59    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(duplicate_literal_removal,[],[f163])).
% 1.66/0.59  fof(f163,plain,(
% 1.66/0.59    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f112,f147])).
% 1.66/0.59  fof(f147,plain,(
% 1.66/0.59    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(resolution,[],[f130,f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f130,plain,(
% 1.66/0.59    m1_subset_1(sK4(sK3,sK2),sK0) | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f129,f128])).
% 1.66/0.59  fof(f128,plain,(
% 1.66/0.59    ~v1_xboole_0(sK0) | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.66/0.59    inference(resolution,[],[f123,f55])).
% 1.66/0.59  fof(f55,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.66/0.59  fof(f123,plain,(
% 1.66/0.59    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(subsumption_resolution,[],[f122,f96])).
% 1.66/0.59  fof(f122,plain,(
% 1.66/0.59    sK0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.66/0.59    inference(superposition,[],[f102,f94])).
% 1.66/0.59  fof(f102,plain,(
% 1.66/0.59    k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f101,f76])).
% 1.66/0.59  fof(f76,plain,(
% 1.66/0.59    v1_relat_1(sK3)),
% 1.66/0.59    inference(resolution,[],[f31,f57])).
% 1.66/0.59  fof(f57,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.59  fof(f101,plain,(
% 1.66/0.59    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f99,f83])).
% 1.66/0.59  fof(f83,plain,(
% 1.66/0.59    v1_relat_1(sK2)),
% 1.66/0.59    inference(resolution,[],[f35,f57])).
% 1.66/0.59  fof(f99,plain,(
% 1.66/0.59    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.66/0.59    inference(resolution,[],[f68,f33])).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    v1_funct_1(sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3)) | sK3 = X0) )),
% 1.66/0.59    inference(resolution,[],[f29,f38])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.59    inference(flattening,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    v1_funct_1(sK3)),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f129,plain,(
% 1.66/0.59    sK2 = sK3 | k1_xboole_0 = sK1 | v1_xboole_0(sK0) | m1_subset_1(sK4(sK3,sK2),sK0)),
% 1.66/0.59    inference(resolution,[],[f123,f52])).
% 1.66/0.59  fof(f52,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.66/0.59  fof(f112,plain,(
% 1.66/0.59    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f111,f76])).
% 1.66/0.59  fof(f111,plain,(
% 1.66/0.59    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f109,f83])).
% 1.66/0.59  fof(f109,plain,(
% 1.66/0.59    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.66/0.59    inference(resolution,[],[f69,f33])).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3) | k1_relat_1(X1) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1) )),
% 1.66/0.59    inference(resolution,[],[f29,f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f244,plain,(
% 1.66/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 1.66/0.59    inference(forward_demodulation,[],[f242,f60])).
% 1.66/0.59  fof(f242,plain,(
% 1.66/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.66/0.59    inference(resolution,[],[f199,f64])).
% 1.66/0.59  fof(f64,plain,(
% 1.66/0.59    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.66/0.59    inference(equality_resolution,[],[f45])).
% 1.66/0.59  fof(f45,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f199,plain,(
% 1.66/0.59    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.66/0.59    inference(backward_demodulation,[],[f30,f198])).
% 1.66/0.59  fof(f205,plain,(
% 1.66/0.59    r2_relset_1(sK0,k1_xboole_0,sK3,sK3)),
% 1.66/0.59    inference(backward_demodulation,[],[f79,f198])).
% 1.66/0.59  fof(f79,plain,(
% 1.66/0.59    r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.66/0.59    inference(resolution,[],[f31,f67])).
% 1.66/0.59  fof(f302,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.66/0.59    inference(duplicate_literal_removal,[],[f301])).
% 1.66/0.59  fof(f301,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.66/0.59    inference(superposition,[],[f267,f249])).
% 1.66/0.59  fof(f249,plain,(
% 1.66/0.59    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 1.66/0.59    inference(subsumption_resolution,[],[f248,f221])).
% 1.66/0.59  fof(f221,plain,(
% 1.66/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.66/0.59    inference(forward_demodulation,[],[f203,f60])).
% 1.66/0.59  fof(f203,plain,(
% 1.66/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.66/0.59    inference(backward_demodulation,[],[f35,f198])).
% 1.66/0.59  fof(f248,plain,(
% 1.66/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.66/0.59    inference(forward_demodulation,[],[f246,f60])).
% 1.66/0.59  fof(f246,plain,(
% 1.66/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.66/0.59    inference(resolution,[],[f202,f64])).
% 1.66/0.59  fof(f202,plain,(
% 1.66/0.59    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.66/0.59    inference(backward_demodulation,[],[f34,f198])).
% 1.66/0.59  fof(f267,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.66/0.59    inference(superposition,[],[f201,f245])).
% 1.66/0.59  fof(f201,plain,(
% 1.66/0.59    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.66/0.59    inference(backward_demodulation,[],[f32,f198])).
% 1.66/0.59  fof(f210,plain,(
% 1.66/0.59    r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 1.66/0.59    inference(backward_demodulation,[],[f86,f198])).
% 1.66/0.59  fof(f389,plain,(
% 1.66/0.59    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.66/0.59    inference(backward_demodulation,[],[f306,f378])).
% 1.66/0.59  fof(f378,plain,(
% 1.66/0.59    sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f375,f344])).
% 1.66/0.59  fof(f344,plain,(
% 1.66/0.59    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.66/0.59    inference(trivial_inequality_removal,[],[f339])).
% 1.66/0.59  fof(f339,plain,(
% 1.66/0.59    k1_xboole_0 != k1_xboole_0 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.66/0.59    inference(backward_demodulation,[],[f322,f334])).
% 1.66/0.59  fof(f334,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relat_1(sK2)),
% 1.66/0.59    inference(subsumption_resolution,[],[f333,f221])).
% 1.66/0.59  fof(f333,plain,(
% 1.66/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.66/0.59    inference(forward_demodulation,[],[f332,f60])).
% 1.66/0.59  fof(f332,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.66/0.59    inference(forward_demodulation,[],[f329,f310])).
% 1.66/0.59  fof(f310,plain,(
% 1.66/0.59    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.66/0.59    inference(backward_demodulation,[],[f209,f303])).
% 1.66/0.59  fof(f209,plain,(
% 1.66/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.66/0.59    inference(backward_demodulation,[],[f84,f198])).
% 1.66/0.59  fof(f329,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.66/0.59    inference(resolution,[],[f307,f62])).
% 1.66/0.59  fof(f62,plain,(
% 1.66/0.59    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.66/0.59    inference(equality_resolution,[],[f47])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f307,plain,(
% 1.66/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.66/0.59    inference(backward_demodulation,[],[f202,f303])).
% 1.66/0.59  fof(f322,plain,(
% 1.66/0.59    k1_xboole_0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.66/0.59    inference(backward_demodulation,[],[f112,f317])).
% 1.66/0.59  fof(f317,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relat_1(sK3)),
% 1.66/0.59    inference(subsumption_resolution,[],[f316,f220])).
% 1.66/0.59  fof(f316,plain,(
% 1.66/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.66/0.59    inference(forward_demodulation,[],[f315,f60])).
% 1.66/0.59  fof(f315,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.66/0.59    inference(forward_demodulation,[],[f312,f308])).
% 1.66/0.59  fof(f308,plain,(
% 1.66/0.59    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.66/0.59    inference(backward_demodulation,[],[f204,f303])).
% 1.66/0.59  fof(f204,plain,(
% 1.66/0.59    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.66/0.59    inference(backward_demodulation,[],[f77,f198])).
% 1.66/0.59  fof(f312,plain,(
% 1.66/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.66/0.59    inference(resolution,[],[f305,f62])).
% 1.66/0.59  fof(f305,plain,(
% 1.66/0.59    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.66/0.59    inference(backward_demodulation,[],[f199,f303])).
% 1.66/0.59  fof(f375,plain,(
% 1.66/0.59    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.66/0.59    inference(resolution,[],[f371,f304])).
% 1.66/0.59  fof(f304,plain,(
% 1.66/0.59    ( ! [X4] : (~m1_subset_1(X4,k1_xboole_0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.66/0.59    inference(backward_demodulation,[],[f28,f303])).
% 1.66/0.59  fof(f371,plain,(
% 1.66/0.59    m1_subset_1(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 1.66/0.59    inference(subsumption_resolution,[],[f370,f369])).
% 1.66/0.59  fof(f369,plain,(
% 1.66/0.59    ~v1_xboole_0(k1_xboole_0) | sK2 = sK3),
% 1.66/0.59    inference(resolution,[],[f342,f55])).
% 1.66/0.59  fof(f342,plain,(
% 1.66/0.59    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 1.66/0.59    inference(trivial_inequality_removal,[],[f341])).
% 1.66/0.59  fof(f341,plain,(
% 1.66/0.59    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 1.66/0.59    inference(backward_demodulation,[],[f328,f334])).
% 1.66/0.59  fof(f328,plain,(
% 1.66/0.59    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2) | sK2 = sK3),
% 1.66/0.59    inference(forward_demodulation,[],[f320,f317])).
% 1.66/0.59  fof(f320,plain,(
% 1.66/0.59    k1_xboole_0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.66/0.59    inference(backward_demodulation,[],[f102,f317])).
% 1.66/0.59  fof(f370,plain,(
% 1.66/0.59    sK2 = sK3 | v1_xboole_0(k1_xboole_0) | m1_subset_1(sK4(sK3,sK2),k1_xboole_0)),
% 1.66/0.59    inference(resolution,[],[f342,f52])).
% 1.66/0.59  fof(f306,plain,(
% 1.66/0.59    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 1.66/0.59    inference(backward_demodulation,[],[f201,f303])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (2859)------------------------------
% 1.66/0.59  % (2859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (2859)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (2859)Memory used [KB]: 6268
% 1.66/0.59  % (2859)Time elapsed: 0.160 s
% 1.66/0.59  % (2859)------------------------------
% 1.66/0.59  % (2859)------------------------------
% 1.66/0.59  % (2879)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.66/0.59  % (2865)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.66/0.59  % (2860)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.66/0.60  % (2861)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.66/0.60  % (2861)Refutation not found, incomplete strategy% (2861)------------------------------
% 1.66/0.60  % (2861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (2861)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (2861)Memory used [KB]: 1663
% 1.66/0.60  % (2861)Time elapsed: 0.183 s
% 1.66/0.60  % (2861)------------------------------
% 1.66/0.60  % (2861)------------------------------
% 1.66/0.60  % (2877)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.66/0.60  % (2862)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.66/0.60  % (2871)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.66/0.61  % (2853)Success in time 0.245 s
%------------------------------------------------------------------------------
