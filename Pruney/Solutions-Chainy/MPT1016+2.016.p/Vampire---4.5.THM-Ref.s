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
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 (2313 expanded)
%              Number of leaves         :   12 ( 448 expanded)
%              Depth                    :   29
%              Number of atoms          :  289 (10988 expanded)
%              Number of equality atoms :   78 (2594 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f278])).

fof(f278,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f261,f112])).

fof(f112,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f111,f71])).

fof(f71,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
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

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f55,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f109,f76])).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f54,f60])).

fof(f54,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f87,f88])).

fof(f88,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f59,f61])).

fof(f61,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
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

fof(f59,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f73,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X1) ) ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f66,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f53,f60])).

fof(f53,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f81,f32])).

fof(f32,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f68,f63])).

fof(f68,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X1) ) ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f52,f60])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f261,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_funct_1(sK1) ),
    inference(backward_demodulation,[],[f31,f260])).

fof(f260,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f224,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f224,plain,(
    ! [X4] : r1_tarski(sK3,X4) ),
    inference(resolution,[],[f207,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f207,plain,(
    ! [X2] : m1_subset_1(sK3,X2) ),
    inference(subsumption_resolution,[],[f195,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f195,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | m1_subset_1(sK3,X2) ) ),
    inference(backward_demodulation,[],[f132,f162])).

fof(f162,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f161,f116])).

fof(f116,plain,(
    sK2 != sK3 ),
    inference(resolution,[],[f112,f31])).

fof(f161,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f149,f147])).

fof(f147,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f146,f115])).

fof(f115,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f112,f30])).

fof(f30,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f146,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f145,f112])).

fof(f145,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f133,f58])).

fof(f58,plain,
    ( ~ sP6(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f57,f35])).

fof(f57,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f43,f50_D])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f50_D])).

fof(f50_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f34,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3)) ) ),
    inference(resolution,[],[f117,f50])).

fof(f117,plain,(
    r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f112,f29])).

fof(f29,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f148,f112])).

fof(f148,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f139,f58])).

fof(f139,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2)) ) ),
    inference(resolution,[],[f118,f50])).

fof(f118,plain,(
    r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f112,f28])).

fof(f28,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X2))
      | m1_subset_1(sK3,X2) ) ),
    inference(resolution,[],[f117,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f31,plain,
    ( ~ v2_funct_1(sK1)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f300,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f243,f46])).

fof(f243,plain,(
    ! [X4] : r1_tarski(sK2,X4) ),
    inference(resolution,[],[f209,f49])).

fof(f209,plain,(
    ! [X2] : m1_subset_1(sK2,X2) ),
    inference(subsumption_resolution,[],[f198,f47])).

fof(f198,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | m1_subset_1(sK2,X2) ) ),
    inference(backward_demodulation,[],[f138,f162])).

fof(f138,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X2))
      | m1_subset_1(sK2,X2) ) ),
    inference(resolution,[],[f118,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (5862)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (5854)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (5854)Refutation not found, incomplete strategy% (5854)------------------------------
% 0.20/0.47  % (5854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5867)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.48  % (5854)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (5854)Memory used [KB]: 10618
% 0.20/0.48  % (5854)Time elapsed: 0.075 s
% 0.20/0.48  % (5854)------------------------------
% 0.20/0.48  % (5854)------------------------------
% 0.20/0.48  % (5856)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (5853)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (5853)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f300,f278])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    k1_xboole_0 != sK2),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    v2_funct_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f55,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f35,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f33,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.50    inference(resolution,[],[f54,f60])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f33,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f87,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f73,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(backward_demodulation,[],[f59,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f35,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f35,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X1)) )),
% 0.20/0.50    inference(resolution,[],[f66,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f53,f60])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f33,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_funct_1(sK1) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(sK1) | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0 | v2_funct_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f81,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f68,f63])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X1)) )),
% 0.20/0.50    inference(resolution,[],[f65,f42])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f52,f60])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f33,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    k1_xboole_0 != sK2 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f31,f260])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    k1_xboole_0 = sK3),
% 0.20/0.50    inference(resolution,[],[f224,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ( ! [X4] : (r1_tarski(sK3,X4)) )),
% 0.20/0.50    inference(resolution,[],[f207,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ( ! [X2] : (m1_subset_1(sK3,X2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | m1_subset_1(sK3,X2)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f132,f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    sK2 != sK3),
% 0.20/0.50    inference(resolution,[],[f112,f31])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f149,f147])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(forward_demodulation,[],[f146,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(resolution,[],[f112,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f112])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f133,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ~sP6(sK1,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f35])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f56,f33])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f34,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.20/0.50    inference(general_splitting,[],[f43,f50_D])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f50_D])).
% 0.20/0.50  fof(f50_D,plain,(
% 0.20/0.50    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.20/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ( ! [X3] : (sP6(X3,sK0) | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3))) )),
% 0.20/0.50    inference(resolution,[],[f117,f50])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    r2_hidden(sK3,sK0)),
% 0.20/0.50    inference(resolution,[],[f112,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | r2_hidden(sK3,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f112])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f139,f58])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X3] : (sP6(X3,sK0) | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2))) )),
% 0.20/0.50    inference(resolution,[],[f118,f50])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    r2_hidden(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f112,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | r2_hidden(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK0,k1_zfmisc_1(X2)) | m1_subset_1(sK3,X2)) )),
% 0.20/0.50    inference(resolution,[],[f117,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | sK2 != sK3),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    k1_xboole_0 = sK2),
% 0.20/0.50    inference(resolution,[],[f243,f46])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    ( ! [X4] : (r1_tarski(sK2,X4)) )),
% 0.20/0.50    inference(resolution,[],[f209,f49])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    ( ! [X2] : (m1_subset_1(sK2,X2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f198,f47])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | m1_subset_1(sK2,X2)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f138,f162])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK0,k1_zfmisc_1(X2)) | m1_subset_1(sK2,X2)) )),
% 0.20/0.50    inference(resolution,[],[f118,f41])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (5853)------------------------------
% 0.20/0.50  % (5853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5853)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (5853)Memory used [KB]: 6268
% 0.20/0.50  % (5853)Time elapsed: 0.087 s
% 0.20/0.50  % (5853)------------------------------
% 0.20/0.50  % (5853)------------------------------
% 0.20/0.51  % (5847)Success in time 0.145 s
%------------------------------------------------------------------------------
