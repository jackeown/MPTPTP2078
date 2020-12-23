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
% DateTime   : Thu Dec  3 13:00:56 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   94 (1344 expanded)
%              Number of leaves         :   15 ( 295 expanded)
%              Depth                    :   21
%              Number of atoms          :  275 (5332 expanded)
%              Number of equality atoms :   81 (1368 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(global_subsumption,[],[f407,f444])).

fof(f444,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f90,f35,f82,f426,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f426,plain,(
    ! [X1] : ~ sP5(X1,sK2) ),
    inference(global_subsumption,[],[f82,f402])).

fof(f402,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | ~ sP5(X1,sK2) ) ),
    inference(backward_demodulation,[],[f177,f385])).

% (16091)Refutation not found, incomplete strategy% (16091)------------------------------
% (16091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16091)Termination reason: Refutation not found, incomplete strategy

% (16091)Memory used [KB]: 10874
% (16091)Time elapsed: 0.201 s
% (16091)------------------------------
% (16091)------------------------------
% (16093)Refutation not found, incomplete strategy% (16093)------------------------------
% (16093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16093)Termination reason: Refutation not found, incomplete strategy

% (16093)Memory used [KB]: 11001
% (16093)Time elapsed: 0.221 s
% (16093)------------------------------
% (16093)------------------------------
fof(f385,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f315,f381])).

fof(f381,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f319,f378])).

fof(f378,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f36,f377])).

fof(f377,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f375,f236])).

fof(f236,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f375,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    inference(cnf_transformation,[],[f18])).

fof(f319,plain,(
    ~ r2_hidden(sK3(k1_xboole_0),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f310,f309])).

fof(f309,plain,(
    k1_xboole_0 = sK7(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f281,f299,f251])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = X0
      | sP5(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X0,sK1)
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f249,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f73,f34])).

fof(f34,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f249,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(sK2))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f35,f90,f243])).

fof(f243,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_1(sK2)
      | r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f75,f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f299,plain,(
    ~ sP5(sK7(sK1,k2_relat_1(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f90,f35,f285,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f285,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f232,f281,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f232,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f37,f230])).

fof(f230,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f38,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f38,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f281,plain,(
    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(global_subsumption,[],[f232,f280])).

fof(f280,plain,
    ( r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f191])).

fof(f191,plain,(
    ! [X2] :
      ( r2_hidden(sK7(X2,k2_relat_1(sK2)),sK1)
      | k2_relat_1(sK2) = X2
      | r2_hidden(sK7(X2,k2_relat_1(sK2)),X2) ) ),
    inference(resolution,[],[f56,f147])).

fof(f147,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK2))
      | r2_hidden(X5,sK1) ) ),
    inference(resolution,[],[f55,f120])).

fof(f120,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f118,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f90,f113,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f113,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f37,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f310,plain,(
    ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f281,f299,f125])).

fof(f315,plain,(
    r2_hidden(sK3(k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f287,f309])).

fof(f287,plain,(
    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f281,f33])).

fof(f33,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f177,plain,(
    ! [X1] :
      ( ~ sP5(X1,sK2)
      | r2_hidden(X1,sK1) ) ),
    inference(global_subsumption,[],[f35,f90,f172])).

fof(f172,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | ~ sP5(X1,sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f72,f147])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f52,f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f407,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f232,f385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.37/0.54  % (16077)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.55  % (16073)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.56  % (16072)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.58  % (16098)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.56/0.58  % (16085)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.58  % (16076)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.58  % (16082)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.59  % (16081)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.59  % (16097)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.59  % (16075)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.59  % (16073)Refutation not found, incomplete strategy% (16073)------------------------------
% 1.56/0.59  % (16073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (16079)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.59  % (16074)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.59  % (16081)Refutation not found, incomplete strategy% (16081)------------------------------
% 1.56/0.59  % (16081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (16096)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.59  % (16082)Refutation not found, incomplete strategy% (16082)------------------------------
% 1.56/0.59  % (16082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (16094)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.60  % (16082)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.60  
% 1.56/0.60  % (16082)Memory used [KB]: 10746
% 1.56/0.60  % (16082)Time elapsed: 0.162 s
% 1.56/0.60  % (16082)------------------------------
% 1.56/0.60  % (16082)------------------------------
% 1.56/0.60  % (16093)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.60  % (16073)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.60  
% 1.56/0.60  % (16073)Memory used [KB]: 11257
% 1.56/0.60  % (16073)Time elapsed: 0.157 s
% 1.56/0.60  % (16073)------------------------------
% 1.56/0.60  % (16073)------------------------------
% 1.56/0.60  % (16088)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.60  % (16092)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.60  % (16095)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.60  % (16099)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.60  % (16078)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.60  % (16089)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.61  % (16086)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.61  % (16084)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.61  % (16080)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.61  % (16083)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.61  % (16087)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.61  % (16071)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.61  % (16100)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.61  % (16081)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16081)Memory used [KB]: 10746
% 1.56/0.61  % (16081)Time elapsed: 0.164 s
% 1.56/0.61  % (16081)------------------------------
% 1.56/0.61  % (16081)------------------------------
% 1.56/0.61  % (16091)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.62  % (16090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.62  % (16088)Refutation not found, incomplete strategy% (16088)------------------------------
% 1.56/0.62  % (16088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (16088)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (16088)Memory used [KB]: 10746
% 1.56/0.62  % (16088)Time elapsed: 0.200 s
% 1.56/0.62  % (16088)------------------------------
% 1.56/0.62  % (16088)------------------------------
% 1.56/0.63  % (16092)Refutation not found, incomplete strategy% (16092)------------------------------
% 1.56/0.63  % (16092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.63  % (16092)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.63  
% 1.56/0.63  % (16092)Memory used [KB]: 1791
% 1.56/0.63  % (16092)Time elapsed: 0.204 s
% 1.56/0.63  % (16092)------------------------------
% 1.56/0.63  % (16092)------------------------------
% 1.56/0.63  % (16095)Refutation found. Thanks to Tanya!
% 1.56/0.63  % SZS status Theorem for theBenchmark
% 1.56/0.63  % SZS output start Proof for theBenchmark
% 1.56/0.63  fof(f447,plain,(
% 1.56/0.63    $false),
% 1.56/0.63    inference(global_subsumption,[],[f407,f444])).
% 1.56/0.63  fof(f444,plain,(
% 1.56/0.63    k1_xboole_0 = k2_relat_1(sK2)),
% 1.56/0.63    inference(unit_resulting_resolution,[],[f90,f35,f82,f426,f46])).
% 1.56/0.63  fof(f46,plain,(
% 1.56/0.63    ( ! [X0,X1] : (sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.56/0.63    inference(cnf_transformation,[],[f21])).
% 1.56/0.63  fof(f21,plain,(
% 1.56/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.63    inference(flattening,[],[f20])).
% 1.56/0.63  fof(f20,plain,(
% 1.56/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.63    inference(ennf_transformation,[],[f9])).
% 1.56/0.63  fof(f9,axiom,(
% 1.56/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.56/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.56/0.63  fof(f426,plain,(
% 1.56/0.63    ( ! [X1] : (~sP5(X1,sK2)) )),
% 1.56/0.63    inference(global_subsumption,[],[f82,f402])).
% 1.56/0.63  fof(f402,plain,(
% 1.56/0.63    ( ! [X1] : (r2_hidden(X1,k1_xboole_0) | ~sP5(X1,sK2)) )),
% 1.56/0.63    inference(backward_demodulation,[],[f177,f385])).
% 1.56/0.63  % (16091)Refutation not found, incomplete strategy% (16091)------------------------------
% 1.56/0.63  % (16091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.63  % (16091)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.63  
% 1.56/0.63  % (16091)Memory used [KB]: 10874
% 1.56/0.63  % (16091)Time elapsed: 0.201 s
% 1.56/0.63  % (16091)------------------------------
% 1.56/0.63  % (16091)------------------------------
% 1.56/0.64  % (16093)Refutation not found, incomplete strategy% (16093)------------------------------
% 1.56/0.64  % (16093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.64  % (16093)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.64  
% 1.56/0.64  % (16093)Memory used [KB]: 11001
% 1.56/0.64  % (16093)Time elapsed: 0.221 s
% 1.56/0.64  % (16093)------------------------------
% 1.56/0.64  % (16093)------------------------------
% 2.29/0.65  fof(f385,plain,(
% 2.29/0.65    k1_xboole_0 = sK1),
% 2.29/0.65    inference(global_subsumption,[],[f315,f381])).
% 2.29/0.65  fof(f381,plain,(
% 2.29/0.65    ~r2_hidden(sK3(k1_xboole_0),sK0) | k1_xboole_0 = sK1),
% 2.29/0.65    inference(superposition,[],[f319,f378])).
% 2.29/0.65  fof(f378,plain,(
% 2.29/0.65    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 2.29/0.65    inference(global_subsumption,[],[f36,f377])).
% 2.29/0.65  fof(f377,plain,(
% 2.29/0.65    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 2.29/0.65    inference(forward_demodulation,[],[f375,f236])).
% 2.29/0.65  fof(f236,plain,(
% 2.29/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f37,f62])).
% 2.29/0.65  fof(f62,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f29])).
% 2.29/0.65  fof(f29,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.29/0.65    inference(ennf_transformation,[],[f12])).
% 2.29/0.65  fof(f12,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.29/0.65  fof(f37,plain,(
% 2.29/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f18,plain,(
% 2.29/0.65    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.29/0.65    inference(flattening,[],[f17])).
% 2.29/0.65  fof(f17,plain,(
% 2.29/0.65    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.29/0.65    inference(ennf_transformation,[],[f16])).
% 2.29/0.65  fof(f16,negated_conjecture,(
% 2.29/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.29/0.65    inference(negated_conjecture,[],[f15])).
% 2.29/0.65  fof(f15,conjecture,(
% 2.29/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 2.29/0.65  fof(f375,plain,(
% 2.29/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.29/0.65    inference(resolution,[],[f70,f37])).
% 2.29/0.65  fof(f70,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f32])).
% 2.29/0.65  fof(f32,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.29/0.65    inference(flattening,[],[f31])).
% 2.29/0.65  fof(f31,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.29/0.65    inference(ennf_transformation,[],[f14])).
% 2.29/0.65  fof(f14,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.29/0.65  fof(f36,plain,(
% 2.29/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f319,plain,(
% 2.29/0.65    ~r2_hidden(sK3(k1_xboole_0),k1_relat_1(sK2))),
% 2.29/0.65    inference(backward_demodulation,[],[f310,f309])).
% 2.29/0.65  fof(f309,plain,(
% 2.29/0.65    k1_xboole_0 = sK7(sK1,k2_relat_1(sK2))),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f281,f299,f251])).
% 2.29/0.65  fof(f251,plain,(
% 2.29/0.65    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = X0 | sP5(X0,sK2)) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f250])).
% 2.29/0.65  fof(f250,plain,(
% 2.29/0.65    ( ! [X0] : (k1_xboole_0 = X0 | ~r2_hidden(X0,sK1) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 2.29/0.65    inference(resolution,[],[f249,f125])).
% 2.29/0.65  fof(f125,plain,(
% 2.29/0.65    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 2.29/0.65    inference(superposition,[],[f73,f34])).
% 2.29/0.65  fof(f34,plain,(
% 2.29/0.65    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f73,plain,(
% 2.29/0.65    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 2.29/0.65    inference(equality_resolution,[],[f41])).
% 2.29/0.65  fof(f41,plain,(
% 2.29/0.65    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f21])).
% 2.29/0.65  fof(f249,plain,(
% 2.29/0.65    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(sK2)) | k1_xboole_0 = X0 | ~r2_hidden(X0,sK1)) )),
% 2.29/0.65    inference(global_subsumption,[],[f35,f90,f243])).
% 2.29/0.65  fof(f243,plain,(
% 2.29/0.65    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_1(sK2) | r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 2.29/0.65    inference(superposition,[],[f75,f34])).
% 2.29/0.65  fof(f75,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f49])).
% 2.29/0.65  fof(f49,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 2.29/0.65    inference(cnf_transformation,[],[f23])).
% 2.29/0.65  fof(f23,plain,(
% 2.29/0.65    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.29/0.65    inference(flattening,[],[f22])).
% 2.29/0.65  fof(f22,plain,(
% 2.29/0.65    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f8])).
% 2.29/0.65  fof(f8,axiom,(
% 2.29/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 2.29/0.65  fof(f299,plain,(
% 2.29/0.65    ~sP5(sK7(sK1,k2_relat_1(sK2)),sK2)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f90,f35,f285,f72])).
% 2.29/0.65  fof(f72,plain,(
% 2.29/0.65    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 2.29/0.65    inference(equality_resolution,[],[f44])).
% 2.29/0.65  fof(f44,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.29/0.65    inference(cnf_transformation,[],[f21])).
% 2.29/0.65  fof(f285,plain,(
% 2.29/0.65    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f232,f281,f57])).
% 2.29/0.65  fof(f57,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(sK7(X0,X1),X0) | X0 = X1) )),
% 2.29/0.65    inference(cnf_transformation,[],[f26])).
% 2.29/0.65  fof(f26,plain,(
% 2.29/0.65    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.29/0.65    inference(ennf_transformation,[],[f1])).
% 2.29/0.65  fof(f1,axiom,(
% 2.29/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.29/0.65  fof(f232,plain,(
% 2.29/0.65    sK1 != k2_relat_1(sK2)),
% 2.29/0.65    inference(global_subsumption,[],[f37,f230])).
% 2.29/0.65  fof(f230,plain,(
% 2.29/0.65    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.29/0.65    inference(superposition,[],[f38,f61])).
% 2.29/0.65  fof(f61,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f28])).
% 2.29/0.65  fof(f28,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.29/0.65    inference(ennf_transformation,[],[f13])).
% 2.29/0.65  fof(f13,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.29/0.65  fof(f38,plain,(
% 2.29/0.65    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f281,plain,(
% 2.29/0.65    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 2.29/0.65    inference(global_subsumption,[],[f232,f280])).
% 2.29/0.65  fof(f280,plain,(
% 2.29/0.65    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 2.29/0.65    inference(factoring,[],[f191])).
% 2.29/0.65  fof(f191,plain,(
% 2.29/0.65    ( ! [X2] : (r2_hidden(sK7(X2,k2_relat_1(sK2)),sK1) | k2_relat_1(sK2) = X2 | r2_hidden(sK7(X2,k2_relat_1(sK2)),X2)) )),
% 2.29/0.65    inference(resolution,[],[f56,f147])).
% 2.29/0.65  fof(f147,plain,(
% 2.29/0.65    ( ! [X5] : (~r2_hidden(X5,k2_relat_1(sK2)) | r2_hidden(X5,sK1)) )),
% 2.29/0.65    inference(resolution,[],[f55,f120])).
% 2.29/0.65  fof(f120,plain,(
% 2.29/0.65    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f118,f58])).
% 2.29/0.65  fof(f58,plain,(
% 2.29/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f4])).
% 2.29/0.65  fof(f4,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.29/0.65  fof(f118,plain,(
% 2.29/0.65    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f90,f113,f54])).
% 2.29/0.65  fof(f54,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f24])).
% 2.29/0.65  fof(f24,plain,(
% 2.29/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.29/0.65    inference(ennf_transformation,[],[f6])).
% 2.29/0.65  fof(f6,axiom,(
% 2.29/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.29/0.65  fof(f113,plain,(
% 2.29/0.65    v5_relat_1(sK2,sK1)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f37,f64])).
% 2.29/0.65  fof(f64,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f30])).
% 2.29/0.65  fof(f30,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.29/0.65    inference(ennf_transformation,[],[f11])).
% 2.29/0.65  fof(f11,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.29/0.65  fof(f55,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f25])).
% 2.29/0.65  fof(f25,plain,(
% 2.29/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f3])).
% 2.29/0.65  fof(f3,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.29/0.65  fof(f56,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0) | X0 = X1) )),
% 2.29/0.65    inference(cnf_transformation,[],[f26])).
% 2.29/0.65  fof(f310,plain,(
% 2.29/0.65    ~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f281,f299,f125])).
% 2.29/0.65  fof(f315,plain,(
% 2.29/0.65    r2_hidden(sK3(k1_xboole_0),sK0)),
% 2.29/0.65    inference(backward_demodulation,[],[f287,f309])).
% 2.29/0.65  fof(f287,plain,(
% 2.29/0.65    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f281,f33])).
% 2.29/0.65  fof(f33,plain,(
% 2.29/0.65    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f177,plain,(
% 2.29/0.65    ( ! [X1] : (~sP5(X1,sK2) | r2_hidden(X1,sK1)) )),
% 2.29/0.65    inference(global_subsumption,[],[f35,f90,f172])).
% 2.29/0.65  fof(f172,plain,(
% 2.29/0.65    ( ! [X1] : (~v1_funct_1(sK2) | ~sP5(X1,sK2) | ~v1_relat_1(sK2) | r2_hidden(X1,sK1)) )),
% 2.29/0.65    inference(resolution,[],[f72,f147])).
% 2.29/0.65  fof(f82,plain,(
% 2.29/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f39,f60])).
% 2.29/0.65  fof(f60,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f27])).
% 2.29/0.65  fof(f27,plain,(
% 2.29/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.29/0.65    inference(ennf_transformation,[],[f10])).
% 2.29/0.65  fof(f10,axiom,(
% 2.29/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.29/0.65  fof(f39,plain,(
% 2.29/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f2])).
% 2.29/0.65  fof(f2,axiom,(
% 2.29/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.29/0.65  fof(f35,plain,(
% 2.29/0.65    v1_funct_1(sK2)),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f90,plain,(
% 2.29/0.65    v1_relat_1(sK2)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f52,f37,f40])).
% 2.29/0.65  fof(f40,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f19])).
% 2.29/0.65  fof(f19,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.29/0.65    inference(ennf_transformation,[],[f5])).
% 2.29/0.65  fof(f5,axiom,(
% 2.29/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.29/0.65  fof(f52,plain,(
% 2.29/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f7])).
% 2.29/0.65  fof(f7,axiom,(
% 2.29/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.29/0.65  fof(f407,plain,(
% 2.29/0.65    k1_xboole_0 != k2_relat_1(sK2)),
% 2.29/0.65    inference(backward_demodulation,[],[f232,f385])).
% 2.29/0.65  % SZS output end Proof for theBenchmark
% 2.29/0.65  % (16095)------------------------------
% 2.29/0.65  % (16095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.65  % (16095)Termination reason: Refutation
% 2.29/0.65  
% 2.29/0.65  % (16095)Memory used [KB]: 6652
% 2.29/0.65  % (16095)Time elapsed: 0.206 s
% 2.29/0.65  % (16095)------------------------------
% 2.29/0.65  % (16095)------------------------------
% 2.29/0.65  % (16070)Success in time 0.299 s
%------------------------------------------------------------------------------
