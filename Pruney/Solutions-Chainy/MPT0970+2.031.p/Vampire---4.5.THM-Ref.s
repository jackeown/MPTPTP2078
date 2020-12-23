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
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  127 (4504 expanded)
%              Number of leaves         :   14 ( 964 expanded)
%              Depth                    :   31
%              Number of atoms          :  335 (17723 expanded)
%              Number of equality atoms :  108 (5006 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f942,plain,(
    $false ),
    inference(resolution,[],[f758,f80])).

fof(f80,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f758,plain,(
    r2_hidden(sK6(sK2,sK4(sK2,k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f680,f756])).

fof(f756,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f729,f745])).

fof(f745,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f722,f723,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f723,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f607,f721])).

fof(f721,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f189,f716])).

fof(f716,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f624,f665])).

fof(f665,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f606,f659])).

fof(f659,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(resolution,[],[f607,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f606,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f603])).

fof(f603,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f570,f499])).

fof(f499,plain,
    ( sP9(sK7(sK1,k1_xboole_0),sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f34,f85,f498])).

fof(f498,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sP9(sK7(sK1,k1_xboole_0),sK2) ),
    inference(resolution,[],[f497,f135])).

fof(f135,plain,(
    ! [X2,X3] :
      ( ~ sP5(X3,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sP9(X3,X2) ) ),
    inference(resolution,[],[f71,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP9(X2,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP9(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f71,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f497,plain,
    ( sP5(sK7(sK1,k1_xboole_0),sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,
    ( sP5(sK7(sK1,k1_xboole_0),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f483,f166])).

fof(f166,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f80])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f483,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sP5(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(global_subsumption,[],[f32,f481])).

fof(f481,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK0)
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f88,f480])).

fof(f480,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f35,f479])).

fof(f479,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f478,f282])).

fof(f282,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f478,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f64,f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f72,f33])).

fof(f33,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f570,plain,(
    ! [X0] :
      ( ~ sP9(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f569,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK10(X0,X2),X2),X0)
      | ~ sP9(X2,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f569,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(global_subsumption,[],[f337,f566])).

fof(f566,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK2,sK1),sK1)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK2) ) ),
    inference(global_subsumption,[],[f290,f563])).

fof(f563,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(sK8(sK2,sK1),sK1)
      | sK1 = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f559,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ sP9(sK8(X0,X1),X0)
      | ~ r2_hidden(sK8(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f559,plain,(
    ! [X0] :
      ( sP9(sK8(sK2,sK1),sK2)
      | ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(global_subsumption,[],[f34,f85,f558])).

fof(f558,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | sP9(sK8(sK2,sK1),sK2) ) ),
    inference(resolution,[],[f493,f135])).

fof(f493,plain,(
    ! [X8] :
      ( sP5(sK8(sK2,sK1),sK2)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X8,sK2) ) ),
    inference(resolution,[],[f483,f337])).

fof(f290,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f36,f289])).

fof(f289,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f37,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f37,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f337,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK2,sK1),sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(global_subsumption,[],[f290,f336])).

fof(f336,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK2,sK1),sK1)
      | sK1 = k2_relat_1(sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(factoring,[],[f322])).

fof(f322,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK8(sK2,X9),sK1)
      | k2_relat_1(sK2) = X9
      | r2_hidden(sK8(sK2,X9),X9)
      | ~ r2_hidden(X10,sK2) ) ),
    inference(resolution,[],[f53,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f124,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f124,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1)
      | ~ sP9(X0,sK2) ) ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f96,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f65,f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP9(sK8(X0,X1),X0)
      | r2_hidden(sK8(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f624,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f290,f603])).

fof(f189,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f179,f188])).

fof(f188,plain,(
    k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f162,f179])).

fof(f162,plain,(
    k1_xboole_0 = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f80,f115,f47])).

fof(f115,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f110,f73])).

fof(f110,plain,(
    ! [X0] : ~ sP9(X0,k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f104,f49])).

fof(f104,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f99,f73])).

fof(f99,plain,(
    ! [X0] : ~ sP9(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f90,f73])).

fof(f90,plain,(
    ! [X0] : ~ sP9(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f80,f49])).

fof(f179,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f164,f163])).

fof(f163,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f95,f115,f47])).

fof(f164,plain,(
    k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f104,f115,f47])).

fof(f607,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f603])).

fof(f722,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f606,f721])).

fof(f729,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f621,f721])).

fof(f621,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f282,f603])).

fof(f680,plain,(
    r2_hidden(sK6(sK2,sK4(sK2,k1_xboole_0)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f673,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK6(X0,X2),k1_relat_1(X0))
      | ~ sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f673,plain,(
    sP5(sK4(sK2,k1_xboole_0),sK2) ),
    inference(unit_resulting_resolution,[],[f85,f34,f80,f624,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (28227)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (28239)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (28239)Refutation not found, incomplete strategy% (28239)------------------------------
% 0.21/0.50  % (28239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28239)Memory used [KB]: 10746
% 0.21/0.51  % (28239)Time elapsed: 0.094 s
% 0.21/0.51  % (28239)------------------------------
% 0.21/0.51  % (28239)------------------------------
% 0.21/0.52  % (28228)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (28223)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28230)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (28233)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28232)Refutation not found, incomplete strategy% (28232)------------------------------
% 0.21/0.52  % (28232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28246)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (28225)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (28222)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (28236)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28245)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (28226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28251)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28247)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28242)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (28224)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28234)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28235)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (28240)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28229)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (28232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28232)Memory used [KB]: 10746
% 0.21/0.55  % (28232)Time elapsed: 0.118 s
% 0.21/0.55  % (28232)------------------------------
% 0.21/0.55  % (28232)------------------------------
% 0.21/0.55  % (28244)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (28248)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (28249)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (28231)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (28238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (28243)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (28241)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (28242)Refutation not found, incomplete strategy% (28242)------------------------------
% 0.21/0.57  % (28242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (28242)Memory used [KB]: 11001
% 0.21/0.57  % (28242)Time elapsed: 0.156 s
% 0.21/0.57  % (28242)------------------------------
% 0.21/0.57  % (28242)------------------------------
% 0.21/0.57  % (28250)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (28246)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f942,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(resolution,[],[f758,f80])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f38,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.58  fof(f758,plain,(
% 0.21/0.58    r2_hidden(sK6(sK2,sK4(sK2,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.58    inference(backward_demodulation,[],[f680,f756])).
% 0.21/0.58  fof(f756,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.58    inference(backward_demodulation,[],[f729,f745])).
% 0.21/0.58  fof(f745,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f722,f723,f75])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(flattening,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.58  fof(f723,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.58    inference(backward_demodulation,[],[f607,f721])).
% 0.21/0.58  fof(f721,plain,(
% 0.21/0.58    k1_xboole_0 = sK0),
% 0.21/0.58    inference(global_subsumption,[],[f189,f716])).
% 0.21/0.58  fof(f716,plain,(
% 0.21/0.58    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.58    inference(superposition,[],[f624,f665])).
% 0.21/0.58  fof(f665,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.58    inference(global_subsumption,[],[f606,f659])).
% 0.21/0.58  fof(f659,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.58    inference(resolution,[],[f607,f77])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f606,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.58    inference(backward_demodulation,[],[f35,f603])).
% 0.21/0.58  fof(f603,plain,(
% 0.21/0.58    k1_xboole_0 = sK1),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f591])).
% 0.21/0.58  fof(f591,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.58    inference(resolution,[],[f570,f499])).
% 0.21/0.58  fof(f499,plain,(
% 0.21/0.58    sP9(sK7(sK1,k1_xboole_0),sK2) | k1_xboole_0 = sK1),
% 0.21/0.58    inference(global_subsumption,[],[f34,f85,f498])).
% 0.21/0.58  fof(f498,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sP9(sK7(sK1,k1_xboole_0),sK2)),
% 0.21/0.58    inference(resolution,[],[f497,f135])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~sP5(X3,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sP9(X3,X2)) )),
% 0.21/0.58    inference(resolution,[],[f71,f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP9(X2,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (sP9(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.58  fof(f497,plain,(
% 0.21/0.58    sP5(sK7(sK1,k1_xboole_0),sK2) | k1_xboole_0 = sK1),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f486])).
% 0.21/0.58  fof(f486,plain,(
% 0.21/0.58    sP5(sK7(sK1,k1_xboole_0),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.58    inference(resolution,[],[f483,f166])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK7(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(resolution,[],[f47,f80])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0) | X0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.58  fof(f483,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | sP5(X0,sK2) | k1_xboole_0 = sK1) )),
% 0.21/0.58    inference(global_subsumption,[],[f32,f481])).
% 0.21/0.58  fof(f481,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | sP5(X0,sK2) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 0.21/0.58    inference(superposition,[],[f88,f480])).
% 0.21/0.58  fof(f480,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.58    inference(global_subsumption,[],[f35,f479])).
% 0.21/0.58  fof(f479,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.58    inference(forward_demodulation,[],[f478,f282])).
% 0.21/0.58  fof(f282,plain,(
% 0.21/0.58    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f36,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.58    inference(negated_conjecture,[],[f14])).
% 0.21/0.58  fof(f14,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.58  fof(f478,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.58    inference(resolution,[],[f64,f36])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.58    inference(superposition,[],[f72,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.21/0.58    inference(equality_resolution,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    v1_relat_1(sK2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f36,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    v1_funct_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f570,plain,(
% 0.21/0.58    ( ! [X0] : (~sP9(X0,sK2) | k1_xboole_0 = sK1) )),
% 0.21/0.58    inference(resolution,[],[f569,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK10(X0,X2),X2),X0) | ~sP9(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f569,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_xboole_0 = sK1) )),
% 0.21/0.58    inference(global_subsumption,[],[f337,f566])).
% 0.21/0.58  fof(f566,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK8(sK2,sK1),sK1) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(global_subsumption,[],[f290,f563])).
% 0.21/0.58  fof(f563,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_xboole_0 = sK1 | ~r2_hidden(sK8(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2)) )),
% 0.21/0.58    inference(resolution,[],[f559,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP9(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f559,plain,(
% 0.21/0.58    ( ! [X0] : (sP9(sK8(sK2,sK1),sK2) | ~r2_hidden(X0,sK2) | k1_xboole_0 = sK1) )),
% 0.21/0.58    inference(global_subsumption,[],[f34,f85,f558])).
% 0.21/0.58  fof(f558,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sP9(sK8(sK2,sK1),sK2)) )),
% 0.21/0.58    inference(resolution,[],[f493,f135])).
% 0.21/0.58  fof(f493,plain,(
% 0.21/0.58    ( ! [X8] : (sP5(sK8(sK2,sK1),sK2) | k1_xboole_0 = sK1 | ~r2_hidden(X8,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f483,f337])).
% 0.21/0.58  fof(f290,plain,(
% 0.21/0.58    sK1 != k2_relat_1(sK2)),
% 0.21/0.58    inference(global_subsumption,[],[f36,f289])).
% 0.21/0.58  fof(f289,plain,(
% 0.21/0.58    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(superposition,[],[f37,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f337,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK8(sK2,sK1),sK1) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(global_subsumption,[],[f290,f336])).
% 0.21/0.58  fof(f336,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK8(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(factoring,[],[f322])).
% 0.21/0.58  fof(f322,plain,(
% 0.21/0.58    ( ! [X10,X9] : (r2_hidden(sK8(sK2,X9),sK1) | k2_relat_1(sK2) = X9 | r2_hidden(sK8(sK2,X9),X9) | ~r2_hidden(X10,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f53,f125])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP9(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X1,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f124,f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f66,f36])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1) | ~sP9(X0,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f122,f49])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X4,X3),sK2) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK1)) )),
% 0.21/0.58    inference(resolution,[],[f68,f97])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f96,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.58    inference(resolution,[],[f65,f36])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(flattening,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.88/0.60  fof(f53,plain,(
% 1.88/0.60    ( ! [X0,X1] : (sP9(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.88/0.60    inference(cnf_transformation,[],[f7])).
% 1.88/0.60  fof(f35,plain,(
% 1.88/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.88/0.60    inference(cnf_transformation,[],[f17])).
% 1.88/0.60  fof(f624,plain,(
% 1.88/0.60    k1_xboole_0 != k2_relat_1(sK2)),
% 1.88/0.60    inference(backward_demodulation,[],[f290,f603])).
% 1.88/0.60  fof(f189,plain,(
% 1.88/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.88/0.60    inference(backward_demodulation,[],[f179,f188])).
% 1.88/0.60  fof(f188,plain,(
% 1.88/0.60    k1_xboole_0 = k2_relat_1(k2_relat_1(k1_xboole_0))),
% 1.88/0.60    inference(forward_demodulation,[],[f162,f179])).
% 1.88/0.60  fof(f162,plain,(
% 1.88/0.60    k1_xboole_0 = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f80,f115,f47])).
% 1.88/0.60  fof(f115,plain,(
% 1.88/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f110,f73])).
% 1.88/0.60  fof(f110,plain,(
% 1.88/0.60    ( ! [X0] : (~sP9(X0,k2_relat_1(k2_relat_1(k1_xboole_0)))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f104,f49])).
% 1.88/0.60  fof(f104,plain,(
% 1.88/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k2_relat_1(k1_xboole_0)))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f99,f73])).
% 1.88/0.60  fof(f99,plain,(
% 1.88/0.60    ( ! [X0] : (~sP9(X0,k2_relat_1(k1_xboole_0))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f95,f49])).
% 1.88/0.60  fof(f95,plain,(
% 1.88/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f90,f73])).
% 1.88/0.60  fof(f90,plain,(
% 1.88/0.60    ( ! [X0] : (~sP9(X0,k1_xboole_0)) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f80,f49])).
% 1.88/0.60  fof(f179,plain,(
% 1.88/0.60    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0))),
% 1.88/0.60    inference(backward_demodulation,[],[f164,f163])).
% 1.88/0.60  fof(f163,plain,(
% 1.88/0.60    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f95,f115,f47])).
% 1.88/0.60  fof(f164,plain,(
% 1.88/0.60    k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f104,f115,f47])).
% 1.88/0.60  fof(f607,plain,(
% 1.88/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.88/0.60    inference(backward_demodulation,[],[f36,f603])).
% 1.88/0.60  fof(f722,plain,(
% 1.88/0.60    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.88/0.60    inference(backward_demodulation,[],[f606,f721])).
% 1.88/0.60  fof(f729,plain,(
% 1.88/0.60    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.88/0.60    inference(backward_demodulation,[],[f621,f721])).
% 1.88/0.60  fof(f621,plain,(
% 1.88/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.88/0.60    inference(backward_demodulation,[],[f282,f603])).
% 1.88/0.60  fof(f680,plain,(
% 1.88/0.60    r2_hidden(sK6(sK2,sK4(sK2,k1_xboole_0)),k1_relat_1(sK2))),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f673,f40])).
% 1.88/0.60  fof(f40,plain,(
% 1.88/0.60    ( ! [X2,X0] : (r2_hidden(sK6(X0,X2),k1_relat_1(X0)) | ~sP5(X2,X0)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f19])).
% 1.88/0.60  fof(f673,plain,(
% 1.88/0.60    sP5(sK4(sK2,k1_xboole_0),sK2)),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f85,f34,f80,f624,f44])).
% 1.88/0.60  fof(f44,plain,(
% 1.88/0.60    ( ! [X0,X1] : (sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.88/0.60    inference(cnf_transformation,[],[f19])).
% 1.88/0.60  % SZS output end Proof for theBenchmark
% 1.88/0.60  % (28246)------------------------------
% 1.88/0.60  % (28246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.60  % (28246)Termination reason: Refutation
% 1.88/0.60  
% 1.88/0.60  % (28246)Memory used [KB]: 6908
% 1.88/0.60  % (28246)Time elapsed: 0.156 s
% 1.88/0.60  % (28246)------------------------------
% 1.88/0.60  % (28246)------------------------------
% 1.88/0.61  % (28220)Success in time 0.243 s
%------------------------------------------------------------------------------
