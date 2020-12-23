%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 (28428 expanded)
%              Number of leaves         :    8 (5373 expanded)
%              Depth                    :   40
%              Number of atoms          :  351 (158372 expanded)
%              Number of equality atoms :  174 (37742 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f212])).

fof(f212,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f154,f204])).

fof(f204,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f203,f179])).

fof(f179,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f152,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f159,f155])).

fof(f155,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f147,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f147,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f29,f145])).

fof(f145,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f129,f76])).

fof(f76,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f33,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f129,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f30,f125])).

fof(f125,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f124,f85])).

fof(f85,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f68,f74])).

fof(f74,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f122,f83])).

fof(f83,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f66,f69])).

fof(f69,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f29,f49])).

fof(f66,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f28,f48])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(superposition,[],[f103,f104])).

fof(f104,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f98,f26])).

fof(f26,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f97,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f91,f83])).

fof(f91,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f73,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f29,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f90,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f88,f78])).

fof(f78,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f77,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f50])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3))
      | sK3 = X0 ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
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

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f102,f73])).

fof(f102,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f100,f78])).

fof(f100,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X1) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1 ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f157,f53])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f146,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f146,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f145])).

fof(f152,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f71,f145])).

fof(f71,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f29,f60])).

fof(f203,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f178,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f163,f156])).

fof(f156,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f150,f53])).

fof(f150,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f33,f145])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f161,f53])).

fof(f161,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f149,f57])).

fof(f149,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f145])).

fof(f178,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f148,f160])).

fof(f148,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f30,f145])).

fof(f154,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f76,f145])).

fof(f265,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f207,f260])).

fof(f260,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f258,f245])).

fof(f245,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f223,f235])).

fof(f235,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f234,f156])).

fof(f234,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f233,f53])).

fof(f233,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f230,f211])).

fof(f211,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f153,f204])).

fof(f153,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f74,f145])).

fof(f230,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f208,f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f208,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f149,f204])).

fof(f223,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f103,f218])).

fof(f218,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f217,f155])).

fof(f217,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f216,f53])).

fof(f216,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f213,f209])).

fof(f209,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f151,f204])).

fof(f151,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f69,f145])).

fof(f213,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f206,f55])).

fof(f206,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f146,f204])).

fof(f258,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f243,f205])).

fof(f205,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(backward_demodulation,[],[f26,f204])).

fof(f243,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f229,f235])).

fof(f229,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f221,f218])).

fof(f221,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f91,f218])).

fof(f207,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f148,f204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (18090)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (18082)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (18082)Refutation not found, incomplete strategy% (18082)------------------------------
% 0.21/0.48  % (18082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18082)Memory used [KB]: 1663
% 0.21/0.48  % (18082)Time elapsed: 0.064 s
% 0.21/0.48  % (18082)------------------------------
% 0.21/0.48  % (18082)------------------------------
% 0.21/0.49  % (18076)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (18079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (18089)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18080)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18100)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (18088)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (18080)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f154,f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f203,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f152,f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(forward_demodulation,[],[f147,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f29,f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f129,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.50    inference(resolution,[],[f33,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f30,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f68,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f33,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f67,f33])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f32,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f122,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f66,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(resolution,[],[f29,f49])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f65,f29])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f28,f48])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | sK2 = sK3),
% 0.21/0.50    inference(superposition,[],[f103,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | k1_xboole_0 = sK1 | sK2 = sK3),
% 0.21/0.50    inference(resolution,[],[f98,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f97,f85])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    sK0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f91,f83])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f29,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f88,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f42])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f33,f50])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.21/0.50    inference(resolution,[],[f61,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3)) | sK3 = X0) )),
% 0.21/0.50    inference(resolution,[],[f27,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f102,f73])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f78])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.21/0.50    inference(resolution,[],[f62,f31])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3) | k1_relat_1(X1) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1) )),
% 0.21/0.50    inference(resolution,[],[f27,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.21/0.50    inference(forward_demodulation,[],[f157,f53])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(resolution,[],[f146,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f28,f145])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    r2_relset_1(sK0,k1_xboole_0,sK3,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f71,f145])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.50    inference(resolution,[],[f29,f60])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f178,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(forward_demodulation,[],[f150,f53])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f33,f145])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.21/0.50    inference(forward_demodulation,[],[f161,f53])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(resolution,[],[f149,f57])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f32,f145])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f148,f160])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f30,f145])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f76,f145])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f207,f260])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f223,f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f234,f156])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f233,f53])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f230,f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f153,f204])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f74,f145])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(resolution,[],[f208,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f149,f204])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f103,f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f217,f155])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f216,f53])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f213,f209])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f151,f204])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f69,f145])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(resolution,[],[f206,f55])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f146,f204])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.21/0.50    inference(resolution,[],[f243,f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f26,f204])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f229,f235])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2) | sK2 = sK3),
% 0.21/0.50    inference(forward_demodulation,[],[f221,f218])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f91,f218])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f148,f204])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (18080)------------------------------
% 0.21/0.50  % (18080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18080)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (18080)Memory used [KB]: 6268
% 0.21/0.50  % (18080)Time elapsed: 0.090 s
% 0.21/0.50  % (18080)------------------------------
% 0.21/0.50  % (18080)------------------------------
% 0.21/0.51  % (18072)Success in time 0.147 s
%------------------------------------------------------------------------------
