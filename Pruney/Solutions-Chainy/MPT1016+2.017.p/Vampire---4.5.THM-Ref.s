%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   93 (2600 expanded)
%              Number of leaves         :    9 ( 503 expanded)
%              Depth                    :   31
%              Number of atoms          :  284 (12421 expanded)
%              Number of equality atoms :   80 (2932 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f293,f54])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
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

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f293,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f292,f108])).

fof(f108,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f105,f27])).

fof(f27,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f64,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f50,f54])).

fof(f50,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f104,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f102,f69])).

fof(f69,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f49,f54])).

fof(f49,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f80,f81])).

fof(f81,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f55,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f66,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X1) ) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f59,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f48,f54])).

fof(f48,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f74,f29])).

fof(f29,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f47,f54])).

fof(f47,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f292,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f290,f30])).

fof(f290,plain,
    ( ~ v1_funct_1(sK1)
    | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f275,f105])).

fof(f275,plain,(
    ! [X3] :
      ( ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(X3,sK3) != k1_funct_1(X3,sK2)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f273,f109])).

fof(f109,plain,(
    sK2 != sK3 ),
    inference(resolution,[],[f105,f28])).

fof(f28,plain,
    ( ~ v2_funct_1(sK1)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f273,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(X3,sK3) != k1_funct_1(X3,sK2)
      | sK2 = sK3
      | ~ v2_funct_1(X3) ) ),
    inference(resolution,[],[f210,f199])).

fof(f199,plain,(
    ! [X1] : r2_hidden(sK2,X1) ),
    inference(subsumption_resolution,[],[f188,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f188,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK2,X1) ) ),
    inference(backward_demodulation,[],[f130,f155])).

fof(f155,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f154,f109])).

fof(f154,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f142,f140])).

fof(f140,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f139,f108])).

fof(f139,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f138,f105])).

fof(f138,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f126,f53])).

fof(f53,plain,
    ( ~ sP6(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f52,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f51,f30])).

fof(f51,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f41,f45_D])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f45_D])).

fof(f45_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f41,plain,(
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

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f126,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3)) ) ),
    inference(resolution,[],[f110,f45])).

fof(f110,plain,(
    r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f105,f26])).

fof(f26,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f142,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f141,f105])).

fof(f141,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f132,f53])).

fof(f132,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2)) ) ),
    inference(resolution,[],[f111,f45])).

fof(f111,plain,(
    r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f105,f25])).

fof(f25,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f130,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK2,X1) ) ),
    inference(resolution,[],[f111,f40])).

fof(f210,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_relat_1(X6))
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k1_funct_1(X6,sK3) != k1_funct_1(X6,X7)
      | sK3 = X7
      | ~ v2_funct_1(X6) ) ),
    inference(resolution,[],[f197,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f197,plain,(
    ! [X1] : r2_hidden(sK3,X1) ),
    inference(subsumption_resolution,[],[f185,f44])).

fof(f185,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK3,X1) ) ),
    inference(backward_demodulation,[],[f124,f155])).

fof(f124,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK3,X1) ) ),
    inference(resolution,[],[f110,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:40:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.45  % (7206)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.50  % (7200)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (7203)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (7201)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.52  % (7222)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (7210)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.52  % (7214)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.52  % (7219)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.52  % (7204)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.52  % (7223)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (7204)Refutation not found, incomplete strategy% (7204)------------------------------
% 0.23/0.53  % (7204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (7204)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (7204)Memory used [KB]: 10618
% 0.23/0.53  % (7204)Time elapsed: 0.066 s
% 0.23/0.53  % (7204)------------------------------
% 0.23/0.53  % (7204)------------------------------
% 0.23/0.53  % (7218)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (7220)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.53  % (7199)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (7215)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.53  % (7198)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (7203)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f294,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f293,f54])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    v1_relat_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f32,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(ennf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.23/0.53    inference(flattening,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.23/0.53    inference(negated_conjecture,[],[f11])).
% 0.23/0.53  fof(f11,conjecture,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.23/0.53  fof(f293,plain,(
% 0.23/0.53    ~v1_relat_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f292,f108])).
% 0.23/0.53  fof(f108,plain,(
% 0.23/0.53    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.23/0.53    inference(resolution,[],[f105,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f105,plain,(
% 0.23/0.53    v2_funct_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f104,f64])).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f50,f54])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f30,f38])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.53    inference(flattening,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    v1_funct_1(sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f104,plain,(
% 0.23/0.53    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f102,f69])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.23/0.53    inference(resolution,[],[f49,f54])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f30,f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f102,plain,(
% 0.23/0.53    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f101])).
% 0.23/0.53  fof(f101,plain,(
% 0.23/0.53    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f80,f81])).
% 0.23/0.53  fof(f81,plain,(
% 0.23/0.53    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f66,f57])).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(backward_demodulation,[],[f55,f56])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.23/0.53    inference(resolution,[],[f32,f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(ennf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(resolution,[],[f32,f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(ennf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X1)) )),
% 0.23/0.53    inference(resolution,[],[f59,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f48,f54])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f30,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f80,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_funct_1(sK1) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0) )),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f76])).
% 0.23/0.53  fof(f76,plain,(
% 0.23/0.53    ( ! [X0] : (v2_funct_1(sK1) | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0 | v2_funct_1(sK1)) )),
% 0.23/0.53    inference(resolution,[],[f74,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f61,f57])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X1)) )),
% 0.23/0.53    inference(resolution,[],[f58,f40])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f47,f54])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f30,f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f292,plain,(
% 0.23/0.53    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f290,f30])).
% 0.23/0.53  fof(f290,plain,(
% 0.23/0.53    ~v1_funct_1(sK1) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f275,f105])).
% 0.23/0.53  fof(f275,plain,(
% 0.23/0.53    ( ! [X3] : (~v2_funct_1(X3) | ~v1_funct_1(X3) | k1_funct_1(X3,sK3) != k1_funct_1(X3,sK2) | ~v1_relat_1(X3)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f273,f109])).
% 0.23/0.53  fof(f109,plain,(
% 0.23/0.53    sK2 != sK3),
% 0.23/0.53    inference(resolution,[],[f105,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ~v2_funct_1(sK1) | sK2 != sK3),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f273,plain,(
% 0.23/0.53    ( ! [X3] : (~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(X3,sK3) != k1_funct_1(X3,sK2) | sK2 = sK3 | ~v2_funct_1(X3)) )),
% 0.23/0.53    inference(resolution,[],[f210,f199])).
% 0.23/0.53  fof(f199,plain,(
% 0.23/0.53    ( ! [X1] : (r2_hidden(sK2,X1)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f188,f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.23/0.53  fof(f188,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK2,X1)) )),
% 0.23/0.53    inference(backward_demodulation,[],[f130,f155])).
% 0.23/0.53  fof(f155,plain,(
% 0.23/0.53    k1_xboole_0 = sK0),
% 0.23/0.53    inference(subsumption_resolution,[],[f154,f109])).
% 0.23/0.53  fof(f154,plain,(
% 0.23/0.53    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f147])).
% 0.23/0.53  fof(f147,plain,(
% 0.23/0.53    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.23/0.53    inference(superposition,[],[f142,f140])).
% 0.23/0.53  fof(f140,plain,(
% 0.23/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.23/0.53    inference(forward_demodulation,[],[f139,f108])).
% 0.23/0.53  fof(f139,plain,(
% 0.23/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0),
% 0.23/0.53    inference(subsumption_resolution,[],[f138,f105])).
% 0.23/0.53  fof(f138,plain,(
% 0.23/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f126,f53])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ~sP6(sK1,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f52,f32])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f51,f30])).
% 0.23/0.53  fof(f51,plain,(
% 0.23/0.53    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.23/0.53    inference(resolution,[],[f31,f46])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.23/0.53    inference(general_splitting,[],[f41,f45_D])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f45_D])).
% 0.23/0.53  fof(f45_D,plain,(
% 0.23/0.53    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.23/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.53    inference(flattening,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.53    inference(ennf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    v1_funct_2(sK1,sK0,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f126,plain,(
% 0.23/0.53    ( ! [X3] : (sP6(X3,sK0) | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3))) )),
% 0.23/0.53    inference(resolution,[],[f110,f45])).
% 0.23/0.53  fof(f110,plain,(
% 0.23/0.53    r2_hidden(sK3,sK0)),
% 0.23/0.53    inference(resolution,[],[f105,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ~v2_funct_1(sK1) | r2_hidden(sK3,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f142,plain,(
% 0.23/0.53    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.23/0.53    inference(subsumption_resolution,[],[f141,f105])).
% 0.23/0.53  fof(f141,plain,(
% 0.23/0.53    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f132,f53])).
% 0.23/0.53  fof(f132,plain,(
% 0.23/0.53    ( ! [X3] : (sP6(X3,sK0) | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2))) )),
% 0.23/0.53    inference(resolution,[],[f111,f45])).
% 0.23/0.53  fof(f111,plain,(
% 0.23/0.53    r2_hidden(sK2,sK0)),
% 0.23/0.53    inference(resolution,[],[f105,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ~v2_funct_1(sK1) | r2_hidden(sK2,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f130,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK2,X1)) )),
% 0.23/0.53    inference(resolution,[],[f111,f40])).
% 0.23/0.53  fof(f210,plain,(
% 0.23/0.53    ( ! [X6,X7] : (~r2_hidden(X7,k1_relat_1(X6)) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k1_funct_1(X6,sK3) != k1_funct_1(X6,X7) | sK3 = X7 | ~v2_funct_1(X6)) )),
% 0.23/0.53    inference(resolution,[],[f197,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f197,plain,(
% 0.23/0.53    ( ! [X1] : (r2_hidden(sK3,X1)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f185,f44])).
% 0.23/0.53  fof(f185,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK3,X1)) )),
% 0.23/0.53    inference(backward_demodulation,[],[f124,f155])).
% 0.23/0.53  fof(f124,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK3,X1)) )),
% 0.23/0.53    inference(resolution,[],[f110,f40])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (7203)------------------------------
% 0.23/0.53  % (7203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (7203)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (7203)Memory used [KB]: 6268
% 0.23/0.53  % (7203)Time elapsed: 0.119 s
% 0.23/0.53  % (7203)------------------------------
% 0.23/0.53  % (7203)------------------------------
% 0.23/0.54  % (7198)Refutation not found, incomplete strategy% (7198)------------------------------
% 0.23/0.54  % (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (7198)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (7198)Memory used [KB]: 10618
% 0.23/0.54  % (7198)Time elapsed: 0.114 s
% 0.23/0.54  % (7198)------------------------------
% 0.23/0.54  % (7198)------------------------------
% 0.23/0.54  % (7194)Success in time 0.165 s
%------------------------------------------------------------------------------
