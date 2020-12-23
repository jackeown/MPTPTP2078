%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:09 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  133 (33129 expanded)
%              Number of leaves         :    9 (6311 expanded)
%              Depth                    :   48
%              Number of atoms          :  368 (186261 expanded)
%              Number of equality atoms :  175 (44683 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(resolution,[],[f283,f154])).

fof(f154,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f148,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f148,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f32,f141])).

fof(f141,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f140,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f139,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f33,f56_D])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP5(X1,X0) ) ),
    inference(cnf_transformation,[],[f56_D])).

fof(f56_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f139,plain,
    ( sP5(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f120,f73])).

fof(f73,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP5(sK1,sK0) ),
    inference(resolution,[],[f32,f56])).

fof(f120,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f29,f116])).

fof(f116,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f115,f76])).

fof(f76,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f65,f71])).

fof(f71,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f115,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f113,f74])).

fof(f74,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f63,f67])).

fof(f67,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f28,f47])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f27,f45])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(superposition,[],[f92,f102])).

fof(f102,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f99,f25])).

fof(f25,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f98,f76])).

fof(f98,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f82,f74])).

fof(f82,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f81,f66])).

fof(f66,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f81,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f79,f70])).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f32,f48])).

fof(f79,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3))
      | sK3 = X0 ) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
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

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f91,f66])).

fof(f91,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f89,f70])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X1) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1 ) ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f283,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f282,f49])).

fof(f282,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f281,f57])).

fof(f281,plain,(
    sP5(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f223,f272])).

fof(f272,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f215,f267])).

fof(f267,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f265,f256])).

fof(f256,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f234,f246])).

fof(f246,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f245,f154])).

fof(f245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f244,f49])).

fof(f244,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f241,f218])).

fof(f218,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f151,f210])).

fof(f210,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f205,f46])).

fof(f205,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f204,f49])).

fof(f204,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ) ),
    inference(resolution,[],[f199,f57])).

fof(f199,plain,
    ( sP5(k1_xboole_0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f198,f195])).

fof(f195,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f172,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f163,f154])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f161,f49])).

fof(f161,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f147,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f147,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f141])).

fof(f172,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f146,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f159,f153])).

fof(f153,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f145,f49])).

fof(f145,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f28,f141])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f157,f49])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f144,f53])).

fof(f144,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f27,f141])).

fof(f146,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f29,f141])).

fof(f198,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sP5(k1_xboole_0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f155,f160])).

fof(f155,plain,
    ( r2_relset_1(sK0,k1_xboole_0,sK3,sK3)
    | sP5(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f150,f141])).

fof(f150,plain,
    ( r2_relset_1(sK0,k1_xboole_0,sK3,sK3)
    | sP5(sK1,sK0) ),
    inference(backward_demodulation,[],[f69,f141])).

fof(f69,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | sP5(sK1,sK0) ),
    inference(resolution,[],[f28,f56])).

fof(f151,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f71,f141])).

fof(f241,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f216,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f216,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f147,f210])).

fof(f234,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f92,f229])).

fof(f229,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f228,f153])).

fof(f228,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f227,f49])).

fof(f227,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f224,f217])).

fof(f217,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f149,f210])).

fof(f149,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f67,f141])).

fof(f224,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f214,f51])).

fof(f214,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f144,f210])).

fof(f265,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f254,f213])).

fof(f213,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(backward_demodulation,[],[f25,f210])).

fof(f254,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f240,f246])).

fof(f240,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f232,f229])).

fof(f232,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f82,f229])).

fof(f215,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f146,f210])).

fof(f223,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | sP5(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f220,f210])).

fof(f220,plain,
    ( sP5(k1_xboole_0,k1_xboole_0)
    | r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f156,f210])).

fof(f156,plain,
    ( r2_relset_1(sK0,k1_xboole_0,sK2,sK2)
    | sP5(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f152,f141])).

fof(f152,plain,
    ( sP5(k1_xboole_0,sK0)
    | r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(backward_demodulation,[],[f73,f141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:23:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (28390)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.31/0.54  % (28370)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.31/0.54  % (28372)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.50/0.57  % (28372)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f285,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(resolution,[],[f283,f154])).
% 1.50/0.57  fof(f154,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(forward_demodulation,[],[f148,f49])).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.57    inference(equality_resolution,[],[f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.57  fof(f148,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f32,f141])).
% 1.50/0.57  fof(f141,plain,(
% 1.50/0.57    k1_xboole_0 = sK1),
% 1.50/0.57    inference(resolution,[],[f140,f46])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.50/0.57  fof(f140,plain,(
% 1.50/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1) )),
% 1.50/0.57    inference(resolution,[],[f139,f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (~sP5(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.57    inference(general_splitting,[],[f33,f56_D])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP5(X1,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f56_D])).
% 1.50/0.57  fof(f56_D,plain,(
% 1.50/0.57    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP5(X1,X0)) )),
% 1.50/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f15])).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.50/0.57  fof(f139,plain,(
% 1.50/0.57    sP5(sK1,sK0) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(resolution,[],[f120,f73])).
% 1.50/0.57  fof(f73,plain,(
% 1.50/0.57    r2_relset_1(sK0,sK1,sK2,sK2) | sP5(sK1,sK0)),
% 1.50/0.57    inference(resolution,[],[f32,f56])).
% 1.50/0.57  fof(f120,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(superposition,[],[f29,f116])).
% 1.50/0.57  fof(f116,plain,(
% 1.50/0.57    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(subsumption_resolution,[],[f115,f76])).
% 1.50/0.57  fof(f76,plain,(
% 1.50/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(superposition,[],[f65,f71])).
% 1.50/0.57  fof(f71,plain,(
% 1.50/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.50/0.57    inference(resolution,[],[f32,f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.57  fof(f65,plain,(
% 1.50/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(subsumption_resolution,[],[f64,f32])).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.57    inference(resolution,[],[f31,f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(flattening,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.50/0.57    inference(flattening,[],[f13])).
% 1.50/0.57  fof(f13,plain,(
% 1.50/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.50/0.57    inference(ennf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.50/0.57    inference(negated_conjecture,[],[f11])).
% 1.50/0.57  fof(f11,conjecture,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.50/0.57  fof(f115,plain,(
% 1.50/0.57    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f114])).
% 1.50/0.57  fof(f114,plain,(
% 1.50/0.57    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(superposition,[],[f113,f74])).
% 1.50/0.57  fof(f74,plain,(
% 1.50/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(superposition,[],[f63,f67])).
% 1.50/0.57  fof(f67,plain,(
% 1.50/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.50/0.57    inference(resolution,[],[f28,f47])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.50/0.57    inference(subsumption_resolution,[],[f62,f28])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.57    inference(resolution,[],[f27,f45])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f113,plain,(
% 1.50/0.57    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f112])).
% 1.50/0.57  fof(f112,plain,(
% 1.50/0.57    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f111])).
% 1.50/0.57  fof(f111,plain,(
% 1.50/0.57    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.50/0.57    inference(superposition,[],[f92,f102])).
% 1.50/0.57  fof(f102,plain,(
% 1.50/0.57    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.50/0.57    inference(resolution,[],[f99,f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f99,plain,(
% 1.50/0.57    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(subsumption_resolution,[],[f98,f76])).
% 1.50/0.57  fof(f98,plain,(
% 1.50/0.57    sK0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.50/0.57    inference(superposition,[],[f82,f74])).
% 1.50/0.57  fof(f82,plain,(
% 1.50/0.57    k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.50/0.57    inference(subsumption_resolution,[],[f81,f66])).
% 1.50/0.57  fof(f66,plain,(
% 1.50/0.57    v1_relat_1(sK3)),
% 1.50/0.57    inference(resolution,[],[f28,f48])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.57  fof(f81,plain,(
% 1.50/0.57    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.50/0.57    inference(subsumption_resolution,[],[f79,f70])).
% 1.50/0.57  fof(f70,plain,(
% 1.50/0.57    v1_relat_1(sK2)),
% 1.50/0.57    inference(resolution,[],[f32,f48])).
% 1.50/0.57  fof(f79,plain,(
% 1.50/0.57    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.50/0.57    inference(resolution,[],[f58,f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    v1_funct_1(sK2)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3)) | sK3 = X0) )),
% 1.50/0.57    inference(resolution,[],[f26,f37])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(flattening,[],[f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    v1_funct_1(sK3)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f92,plain,(
% 1.50/0.57    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3),
% 1.50/0.57    inference(subsumption_resolution,[],[f91,f66])).
% 1.50/0.57  fof(f91,plain,(
% 1.50/0.57    ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.50/0.57    inference(subsumption_resolution,[],[f89,f70])).
% 1.50/0.57  fof(f89,plain,(
% 1.50/0.57    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.50/0.57    inference(resolution,[],[f59,f30])).
% 1.50/0.57  fof(f59,plain,(
% 1.50/0.57    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3) | k1_relat_1(X1) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1) )),
% 1.50/0.57    inference(resolution,[],[f26,f38])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f283,plain,(
% 1.50/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.50/0.57    inference(forward_demodulation,[],[f282,f49])).
% 1.50/0.57  fof(f282,plain,(
% 1.50/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.50/0.57    inference(resolution,[],[f281,f57])).
% 1.50/0.57  fof(f281,plain,(
% 1.50/0.57    sP5(k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(resolution,[],[f223,f272])).
% 1.50/0.57  fof(f272,plain,(
% 1.50/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.50/0.57    inference(backward_demodulation,[],[f215,f267])).
% 1.50/0.57  fof(f267,plain,(
% 1.50/0.57    sK2 = sK3),
% 1.50/0.57    inference(subsumption_resolution,[],[f265,f256])).
% 1.50/0.57  fof(f256,plain,(
% 1.50/0.57    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f251])).
% 1.50/0.57  fof(f251,plain,(
% 1.50/0.57    k1_xboole_0 != k1_xboole_0 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.50/0.57    inference(backward_demodulation,[],[f234,f246])).
% 1.50/0.57  fof(f246,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(sK2)),
% 1.50/0.57    inference(subsumption_resolution,[],[f245,f154])).
% 1.50/0.57  fof(f245,plain,(
% 1.50/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.50/0.57    inference(forward_demodulation,[],[f244,f49])).
% 1.50/0.57  fof(f244,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.50/0.57    inference(forward_demodulation,[],[f241,f218])).
% 1.50/0.57  fof(f218,plain,(
% 1.50/0.57    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.50/0.57    inference(backward_demodulation,[],[f151,f210])).
% 1.50/0.57  fof(f210,plain,(
% 1.50/0.57    k1_xboole_0 = sK0),
% 1.50/0.57    inference(resolution,[],[f205,f46])).
% 1.50/0.57  fof(f205,plain,(
% 1.50/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0) )),
% 1.50/0.57    inference(forward_demodulation,[],[f204,f49])).
% 1.50/0.57  fof(f204,plain,(
% 1.50/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))) )),
% 1.50/0.57    inference(resolution,[],[f199,f57])).
% 1.50/0.57  fof(f199,plain,(
% 1.50/0.57    sP5(k1_xboole_0,sK0) | k1_xboole_0 = sK0),
% 1.50/0.57    inference(subsumption_resolution,[],[f198,f195])).
% 1.50/0.57  fof(f195,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f194])).
% 1.50/0.57  fof(f194,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.50/0.57    inference(superposition,[],[f172,f164])).
% 1.50/0.57  fof(f164,plain,(
% 1.50/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 1.50/0.57    inference(subsumption_resolution,[],[f163,f154])).
% 1.50/0.57  fof(f163,plain,(
% 1.50/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.50/0.57    inference(forward_demodulation,[],[f161,f49])).
% 1.50/0.57  fof(f161,plain,(
% 1.50/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.50/0.57    inference(resolution,[],[f147,f53])).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.50/0.57    inference(equality_resolution,[],[f41])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f147,plain,(
% 1.50/0.57    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f31,f141])).
% 1.50/0.57  fof(f172,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.50/0.57    inference(superposition,[],[f146,f160])).
% 1.50/0.57  fof(f160,plain,(
% 1.50/0.57    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.50/0.57    inference(subsumption_resolution,[],[f159,f153])).
% 1.50/0.57  fof(f153,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.50/0.57    inference(forward_demodulation,[],[f145,f49])).
% 1.50/0.57  fof(f145,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f28,f141])).
% 1.50/0.57  fof(f159,plain,(
% 1.50/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 1.50/0.57    inference(forward_demodulation,[],[f157,f49])).
% 1.50/0.57  fof(f157,plain,(
% 1.50/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.50/0.57    inference(resolution,[],[f144,f53])).
% 1.50/0.57  fof(f144,plain,(
% 1.50/0.57    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f27,f141])).
% 1.50/0.57  fof(f146,plain,(
% 1.50/0.57    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.50/0.57    inference(backward_demodulation,[],[f29,f141])).
% 1.50/0.57  fof(f198,plain,(
% 1.50/0.57    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | sP5(k1_xboole_0,sK0) | k1_xboole_0 = sK0),
% 1.50/0.57    inference(superposition,[],[f155,f160])).
% 1.50/0.57  fof(f155,plain,(
% 1.50/0.57    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) | sP5(k1_xboole_0,sK0)),
% 1.50/0.57    inference(forward_demodulation,[],[f150,f141])).
% 1.50/0.57  fof(f150,plain,(
% 1.50/0.57    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) | sP5(sK1,sK0)),
% 1.50/0.57    inference(backward_demodulation,[],[f69,f141])).
% 1.50/0.57  fof(f69,plain,(
% 1.50/0.57    r2_relset_1(sK0,sK1,sK3,sK3) | sP5(sK1,sK0)),
% 1.50/0.57    inference(resolution,[],[f28,f56])).
% 1.50/0.57  fof(f151,plain,(
% 1.50/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.50/0.57    inference(backward_demodulation,[],[f71,f141])).
% 1.50/0.57  fof(f241,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.50/0.57    inference(resolution,[],[f216,f51])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.50/0.57    inference(equality_resolution,[],[f43])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f216,plain,(
% 1.50/0.57    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f147,f210])).
% 1.50/0.57  fof(f234,plain,(
% 1.50/0.57    k1_xboole_0 != k1_relat_1(sK2) | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3),
% 1.50/0.57    inference(backward_demodulation,[],[f92,f229])).
% 1.50/0.57  fof(f229,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(sK3)),
% 1.50/0.57    inference(subsumption_resolution,[],[f228,f153])).
% 1.50/0.57  fof(f228,plain,(
% 1.50/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.50/0.57    inference(forward_demodulation,[],[f227,f49])).
% 1.50/0.57  fof(f227,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.50/0.57    inference(forward_demodulation,[],[f224,f217])).
% 1.50/0.57  fof(f217,plain,(
% 1.50/0.57    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.50/0.57    inference(backward_demodulation,[],[f149,f210])).
% 1.50/0.57  fof(f149,plain,(
% 1.50/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 1.50/0.57    inference(backward_demodulation,[],[f67,f141])).
% 1.50/0.57  fof(f224,plain,(
% 1.50/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.50/0.57    inference(resolution,[],[f214,f51])).
% 1.50/0.57  fof(f214,plain,(
% 1.50/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f144,f210])).
% 1.50/0.57  fof(f265,plain,(
% 1.50/0.57    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.50/0.57    inference(resolution,[],[f254,f213])).
% 1.50/0.57  fof(f213,plain,(
% 1.50/0.57    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.50/0.57    inference(backward_demodulation,[],[f25,f210])).
% 1.50/0.57  fof(f254,plain,(
% 1.50/0.57    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f253])).
% 1.50/0.57  fof(f253,plain,(
% 1.50/0.57    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK3,sK2),k1_xboole_0) | sK2 = sK3),
% 1.50/0.57    inference(backward_demodulation,[],[f240,f246])).
% 1.50/0.57  fof(f240,plain,(
% 1.50/0.57    r2_hidden(sK4(sK3,sK2),k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK2) | sK2 = sK3),
% 1.50/0.57    inference(forward_demodulation,[],[f232,f229])).
% 1.50/0.57  fof(f232,plain,(
% 1.50/0.57    k1_xboole_0 != k1_relat_1(sK2) | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3),
% 1.50/0.57    inference(backward_demodulation,[],[f82,f229])).
% 1.50/0.57  fof(f215,plain,(
% 1.50/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 1.50/0.57    inference(backward_demodulation,[],[f146,f210])).
% 1.50/0.57  fof(f223,plain,(
% 1.50/0.57    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) | sP5(k1_xboole_0,k1_xboole_0)),
% 1.50/0.57    inference(forward_demodulation,[],[f220,f210])).
% 1.50/0.57  fof(f220,plain,(
% 1.50/0.57    sP5(k1_xboole_0,k1_xboole_0) | r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 1.50/0.57    inference(backward_demodulation,[],[f156,f210])).
% 1.50/0.57  fof(f156,plain,(
% 1.50/0.57    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) | sP5(k1_xboole_0,sK0)),
% 1.50/0.57    inference(forward_demodulation,[],[f152,f141])).
% 1.50/0.57  fof(f152,plain,(
% 1.50/0.57    sP5(k1_xboole_0,sK0) | r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.50/0.57    inference(backward_demodulation,[],[f73,f141])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (28372)------------------------------
% 1.50/0.57  % (28372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (28372)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (28372)Memory used [KB]: 6268
% 1.50/0.57  % (28372)Time elapsed: 0.131 s
% 1.50/0.57  % (28372)------------------------------
% 1.50/0.57  % (28372)------------------------------
% 1.50/0.57  % (28368)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.57  % (28389)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.50/0.57  % (28392)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.50/0.58  % (28380)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.50/0.58  % (28378)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.59  % (28366)Success in time 0.221 s
%------------------------------------------------------------------------------
