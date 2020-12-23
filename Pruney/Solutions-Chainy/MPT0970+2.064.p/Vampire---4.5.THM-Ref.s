%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:57 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   91 (1393 expanded)
%              Number of leaves         :   12 ( 292 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 (5988 expanded)
%              Number of equality atoms :   83 (1615 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1103,plain,(
    $false ),
    inference(resolution,[],[f1079,f90])).

fof(f90,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(unit_resulting_resolution,[],[f86,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f86,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1079,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1027,f1078])).

fof(f1078,plain,(
    k1_xboole_0 = sK4(sK2,k1_xboole_0) ),
    inference(global_subsumption,[],[f1028,f1077])).

fof(f1077,plain,
    ( sP5(sK4(sK2,k1_xboole_0),sK2)
    | k1_xboole_0 = sK4(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1076,f887])).

fof(f887,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f789,f883])).

fof(f883,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f788,f324])).

fof(f324,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sP5(X0,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(global_subsumption,[],[f28,f313])).

fof(f313,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK0)
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f107,f312])).

fof(f312,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f31,f311])).

fof(f311,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f308,f139])).

fof(f139,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f32,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f308,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f64,f29])).

fof(f29,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f788,plain,(
    r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(global_subsumption,[],[f145,f787])).

fof(f787,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f515])).

fof(f515,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK2,X3),sK1)
      | r2_hidden(sK4(sK2,X3),X3)
      | k2_relat_1(sK2) = X3 ) ),
    inference(global_subsumption,[],[f30,f79,f508])).

fof(f508,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK2,X3),sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X3),X3)
      | k2_relat_1(sK2) = X3 ) ),
    inference(resolution,[],[f502,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f502,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f30,f79,f499])).

fof(f499,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(X0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f131,f162])).

fof(f162,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f161,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f161,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f153,f142])).

fof(f142,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f153,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f131,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),X4)
      | ~ sP5(X3,X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X4)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f46,f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f145,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f32,f144])).

fof(f144,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f33,f54])).

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f789,plain,(
    ~ sP5(sK4(sK2,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f79,f30,f145,f788,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sP5(sK4(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1076,plain,
    ( k1_xboole_0 = sK4(sK2,k1_xboole_0)
    | sP5(sK4(sK2,sK1),sK2) ),
    inference(forward_demodulation,[],[f884,f887])).

fof(f884,plain,
    ( k1_xboole_0 = sK4(sK2,sK1)
    | sP5(sK4(sK2,sK1),sK2) ),
    inference(resolution,[],[f788,f185])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = X0
      | sP5(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X0,sK1)
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f178,f107])).

fof(f178,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(sK2))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f30,f79,f173])).

fof(f173,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_1(sK2)
      | r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f66,f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f1028,plain,(
    ~ sP5(sK4(sK2,k1_xboole_0),sK2) ),
    inference(backward_demodulation,[],[f789,f887])).

fof(f1027,plain,(
    r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f788,f887])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (5169)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5185)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (5172)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (5177)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5171)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5180)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (5165)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (5166)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5165)Refutation not found, incomplete strategy% (5165)------------------------------
% 0.21/0.53  % (5165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5165)Memory used [KB]: 1663
% 0.21/0.53  % (5165)Time elapsed: 0.118 s
% 0.21/0.53  % (5165)------------------------------
% 0.21/0.53  % (5165)------------------------------
% 0.21/0.53  % (5168)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5187)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (5179)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (5182)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (5167)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5192)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (5182)Refutation not found, incomplete strategy% (5182)------------------------------
% 0.21/0.54  % (5182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5182)Memory used [KB]: 10618
% 0.21/0.54  % (5182)Time elapsed: 0.138 s
% 0.21/0.54  % (5182)------------------------------
% 0.21/0.54  % (5182)------------------------------
% 0.21/0.54  % (5190)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5174)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (5184)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (5191)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (5175)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (5183)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (5176)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (5175)Refutation not found, incomplete strategy% (5175)------------------------------
% 0.21/0.56  % (5175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5175)Memory used [KB]: 10746
% 0.21/0.56  % (5175)Time elapsed: 0.159 s
% 0.21/0.56  % (5175)------------------------------
% 0.21/0.56  % (5175)------------------------------
% 0.21/0.56  % (5170)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (5194)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (5186)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (5178)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (5181)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (5173)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (5193)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (5188)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (5189)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.03/0.67  % (5195)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.03/0.70  % (5196)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.65/0.71  % (5197)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.65/0.73  % (5189)Refutation found. Thanks to Tanya!
% 2.65/0.73  % SZS status Theorem for theBenchmark
% 2.65/0.73  % SZS output start Proof for theBenchmark
% 2.65/0.73  fof(f1103,plain,(
% 2.65/0.73    $false),
% 2.65/0.73    inference(resolution,[],[f1079,f90])).
% 2.65/0.73  fof(f90,plain,(
% 2.65/0.73    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 2.65/0.73    inference(unit_resulting_resolution,[],[f86,f52])).
% 2.65/0.73  fof(f52,plain,(
% 2.65/0.73    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f22])).
% 2.65/0.73  fof(f22,plain,(
% 2.65/0.73    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.65/0.73    inference(ennf_transformation,[],[f7])).
% 2.65/0.73  fof(f7,axiom,(
% 2.65/0.73    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.65/0.73  fof(f86,plain,(
% 2.65/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.65/0.73    inference(duplicate_literal_removal,[],[f85])).
% 2.65/0.73  fof(f85,plain,(
% 2.65/0.73    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.65/0.73    inference(resolution,[],[f49,f48])).
% 2.65/0.73  fof(f48,plain,(
% 2.65/0.73    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f21])).
% 2.65/0.73  fof(f21,plain,(
% 2.65/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.65/0.73    inference(ennf_transformation,[],[f1])).
% 2.65/0.73  fof(f1,axiom,(
% 2.65/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.65/0.73  fof(f49,plain,(
% 2.65/0.73    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f21])).
% 2.65/0.73  fof(f1079,plain,(
% 2.65/0.73    r2_hidden(k1_xboole_0,k1_xboole_0)),
% 2.65/0.73    inference(backward_demodulation,[],[f1027,f1078])).
% 2.65/0.73  fof(f1078,plain,(
% 2.65/0.73    k1_xboole_0 = sK4(sK2,k1_xboole_0)),
% 2.65/0.73    inference(global_subsumption,[],[f1028,f1077])).
% 2.65/0.73  fof(f1077,plain,(
% 2.65/0.73    sP5(sK4(sK2,k1_xboole_0),sK2) | k1_xboole_0 = sK4(sK2,k1_xboole_0)),
% 2.65/0.73    inference(forward_demodulation,[],[f1076,f887])).
% 2.65/0.73  fof(f887,plain,(
% 2.65/0.73    k1_xboole_0 = sK1),
% 2.65/0.73    inference(global_subsumption,[],[f789,f883])).
% 2.65/0.73  fof(f883,plain,(
% 2.65/0.73    sP5(sK4(sK2,sK1),sK2) | k1_xboole_0 = sK1),
% 2.65/0.73    inference(resolution,[],[f788,f324])).
% 2.65/0.73  fof(f324,plain,(
% 2.65/0.73    ( ! [X0] : (~r2_hidden(X0,sK1) | sP5(X0,sK2) | k1_xboole_0 = sK1) )),
% 2.65/0.73    inference(global_subsumption,[],[f28,f313])).
% 2.65/0.73  fof(f313,plain,(
% 2.65/0.73    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | sP5(X0,sK2) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 2.65/0.73    inference(superposition,[],[f107,f312])).
% 2.65/0.73  fof(f312,plain,(
% 2.65/0.73    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 2.65/0.73    inference(global_subsumption,[],[f31,f311])).
% 2.65/0.73  fof(f311,plain,(
% 2.65/0.73    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 2.65/0.73    inference(forward_demodulation,[],[f308,f139])).
% 2.65/0.73  fof(f139,plain,(
% 2.65/0.73    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.65/0.73    inference(unit_resulting_resolution,[],[f32,f53])).
% 2.65/0.73  fof(f53,plain,(
% 2.65/0.73    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.73    inference(cnf_transformation,[],[f23])).
% 2.65/0.73  fof(f23,plain,(
% 2.65/0.73    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.73    inference(ennf_transformation,[],[f9])).
% 2.65/0.73  fof(f9,axiom,(
% 2.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.65/0.73  fof(f32,plain,(
% 2.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.65/0.73    inference(cnf_transformation,[],[f15])).
% 2.65/0.73  fof(f15,plain,(
% 2.65/0.73    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.65/0.73    inference(flattening,[],[f14])).
% 2.65/0.73  fof(f14,plain,(
% 2.65/0.73    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.65/0.73    inference(ennf_transformation,[],[f13])).
% 2.65/0.73  fof(f13,negated_conjecture,(
% 2.65/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.65/0.73    inference(negated_conjecture,[],[f12])).
% 2.65/0.73  fof(f12,conjecture,(
% 2.65/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 2.65/0.73  fof(f308,plain,(
% 2.65/0.73    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.65/0.73    inference(resolution,[],[f61,f32])).
% 2.65/0.73  fof(f61,plain,(
% 2.65/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f27])).
% 2.65/0.73  fof(f27,plain,(
% 2.65/0.73    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.73    inference(flattening,[],[f26])).
% 2.65/0.73  fof(f26,plain,(
% 2.65/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.73    inference(ennf_transformation,[],[f11])).
% 2.65/0.73  fof(f11,axiom,(
% 2.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.65/0.73  fof(f31,plain,(
% 2.65/0.73    v1_funct_2(sK2,sK0,sK1)),
% 2.65/0.73    inference(cnf_transformation,[],[f15])).
% 2.65/0.73  fof(f107,plain,(
% 2.65/0.73    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 2.65/0.73    inference(superposition,[],[f64,f29])).
% 2.65/0.73  fof(f29,plain,(
% 2.65/0.73    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f15])).
% 2.65/0.73  fof(f64,plain,(
% 2.65/0.73    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 2.65/0.73    inference(equality_resolution,[],[f35])).
% 2.65/0.73  fof(f35,plain,(
% 2.65/0.73    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f18])).
% 2.65/0.73  fof(f18,plain,(
% 2.65/0.73    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.73    inference(flattening,[],[f17])).
% 2.65/0.73  fof(f17,plain,(
% 2.65/0.73    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.73    inference(ennf_transformation,[],[f6])).
% 2.65/0.73  fof(f6,axiom,(
% 2.65/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 2.65/0.73  fof(f28,plain,(
% 2.65/0.73    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f15])).
% 2.65/0.73  fof(f788,plain,(
% 2.65/0.73    r2_hidden(sK4(sK2,sK1),sK1)),
% 2.65/0.73    inference(global_subsumption,[],[f145,f787])).
% 2.65/0.73  fof(f787,plain,(
% 2.65/0.73    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2)),
% 2.65/0.73    inference(factoring,[],[f515])).
% 2.65/0.73  fof(f515,plain,(
% 2.65/0.73    ( ! [X3] : (r2_hidden(sK4(sK2,X3),sK1) | r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) )),
% 2.65/0.73    inference(global_subsumption,[],[f30,f79,f508])).
% 2.65/0.73  fof(f508,plain,(
% 2.65/0.73    ( ! [X3] : (r2_hidden(sK4(sK2,X3),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) )),
% 2.65/0.73    inference(resolution,[],[f502,f40])).
% 2.65/0.73  fof(f40,plain,(
% 2.65/0.73    ( ! [X0,X1] : (sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 2.65/0.73    inference(cnf_transformation,[],[f18])).
% 2.65/0.73  fof(f502,plain,(
% 2.65/0.73    ( ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,sK1)) )),
% 2.65/0.73    inference(global_subsumption,[],[f30,f79,f499])).
% 2.65/0.73  fof(f499,plain,(
% 2.65/0.73    ( ! [X0] : (~sP5(X0,sK2) | ~v1_relat_1(sK2) | r2_hidden(X0,sK1) | ~v1_funct_1(sK2)) )),
% 2.65/0.73    inference(resolution,[],[f131,f162])).
% 2.65/0.73  fof(f162,plain,(
% 2.65/0.73    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.65/0.73    inference(unit_resulting_resolution,[],[f161,f51])).
% 2.65/0.73  fof(f51,plain,(
% 2.65/0.73    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.65/0.73    inference(cnf_transformation,[],[f2])).
% 2.65/0.73  fof(f2,axiom,(
% 2.65/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.65/0.73  fof(f161,plain,(
% 2.65/0.73    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 2.65/0.73    inference(forward_demodulation,[],[f153,f142])).
% 2.65/0.73  fof(f142,plain,(
% 2.65/0.73    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.65/0.73    inference(unit_resulting_resolution,[],[f32,f54])).
% 2.65/0.73  fof(f54,plain,(
% 2.65/0.73    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.73    inference(cnf_transformation,[],[f24])).
% 2.65/0.73  fof(f24,plain,(
% 2.65/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.73    inference(ennf_transformation,[],[f10])).
% 2.65/0.73  fof(f10,axiom,(
% 2.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.65/0.73  fof(f153,plain,(
% 2.65/0.73    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 2.65/0.73    inference(unit_resulting_resolution,[],[f32,f55])).
% 2.65/0.73  fof(f55,plain,(
% 2.65/0.73    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.73    inference(cnf_transformation,[],[f25])).
% 2.65/0.73  fof(f25,plain,(
% 2.65/0.73    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.73    inference(ennf_transformation,[],[f8])).
% 2.65/0.73  fof(f8,axiom,(
% 2.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.65/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 2.65/0.75  fof(f131,plain,(
% 2.65/0.75    ( ! [X4,X2,X3] : (~r1_tarski(k2_relat_1(X2),X4) | ~sP5(X3,X2) | ~v1_relat_1(X2) | r2_hidden(X3,X4) | ~v1_funct_1(X2)) )),
% 2.65/0.75    inference(resolution,[],[f63,f47])).
% 2.65/0.75  fof(f47,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.65/0.75    inference(cnf_transformation,[],[f21])).
% 2.65/0.75  fof(f63,plain,(
% 2.65/0.75    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 2.65/0.75    inference(equality_resolution,[],[f38])).
% 2.65/0.75  fof(f38,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.65/0.75    inference(cnf_transformation,[],[f18])).
% 2.65/0.75  fof(f79,plain,(
% 2.65/0.75    v1_relat_1(sK2)),
% 2.65/0.75    inference(unit_resulting_resolution,[],[f46,f32,f34])).
% 2.65/0.75  fof(f34,plain,(
% 2.65/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.65/0.75    inference(cnf_transformation,[],[f16])).
% 2.65/0.75  fof(f16,plain,(
% 2.65/0.75    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.65/0.75    inference(ennf_transformation,[],[f3])).
% 2.65/0.75  fof(f3,axiom,(
% 2.65/0.75    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.65/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.65/0.75  fof(f46,plain,(
% 2.65/0.75    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f4])).
% 2.65/0.75  fof(f4,axiom,(
% 2.65/0.75    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.65/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.65/0.75  fof(f30,plain,(
% 2.65/0.75    v1_funct_1(sK2)),
% 2.65/0.75    inference(cnf_transformation,[],[f15])).
% 2.65/0.75  fof(f145,plain,(
% 2.65/0.75    sK1 != k2_relat_1(sK2)),
% 2.65/0.75    inference(global_subsumption,[],[f32,f144])).
% 2.65/0.75  fof(f144,plain,(
% 2.65/0.75    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.65/0.75    inference(superposition,[],[f33,f54])).
% 2.65/0.75  fof(f33,plain,(
% 2.65/0.75    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 2.65/0.75    inference(cnf_transformation,[],[f15])).
% 2.65/0.75  fof(f789,plain,(
% 2.65/0.75    ~sP5(sK4(sK2,sK1),sK2)),
% 2.65/0.75    inference(unit_resulting_resolution,[],[f79,f30,f145,f788,f41])).
% 2.65/0.75  fof(f41,plain,(
% 2.65/0.75    ( ! [X0,X1] : (~sP5(sK4(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 2.65/0.75    inference(cnf_transformation,[],[f18])).
% 2.65/0.75  fof(f1076,plain,(
% 2.65/0.75    k1_xboole_0 = sK4(sK2,k1_xboole_0) | sP5(sK4(sK2,sK1),sK2)),
% 2.65/0.75    inference(forward_demodulation,[],[f884,f887])).
% 2.65/0.75  fof(f884,plain,(
% 2.65/0.75    k1_xboole_0 = sK4(sK2,sK1) | sP5(sK4(sK2,sK1),sK2)),
% 2.65/0.75    inference(resolution,[],[f788,f185])).
% 2.65/0.75  fof(f185,plain,(
% 2.65/0.75    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = X0 | sP5(X0,sK2)) )),
% 2.65/0.75    inference(duplicate_literal_removal,[],[f182])).
% 2.65/0.75  fof(f182,plain,(
% 2.65/0.75    ( ! [X0] : (k1_xboole_0 = X0 | ~r2_hidden(X0,sK1) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 2.65/0.75    inference(resolution,[],[f178,f107])).
% 2.65/0.75  fof(f178,plain,(
% 2.65/0.75    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(sK2)) | k1_xboole_0 = X0 | ~r2_hidden(X0,sK1)) )),
% 2.65/0.75    inference(global_subsumption,[],[f30,f79,f173])).
% 2.65/0.75  fof(f173,plain,(
% 2.65/0.75    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_1(sK2) | r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 2.65/0.75    inference(superposition,[],[f66,f29])).
% 2.65/0.75  fof(f66,plain,(
% 2.65/0.75    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.65/0.75    inference(equality_resolution,[],[f43])).
% 2.65/0.75  fof(f43,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 2.65/0.75    inference(cnf_transformation,[],[f20])).
% 2.65/0.75  fof(f20,plain,(
% 2.65/0.75    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.75    inference(flattening,[],[f19])).
% 2.65/0.75  fof(f19,plain,(
% 2.65/0.75    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.75    inference(ennf_transformation,[],[f5])).
% 2.65/0.75  fof(f5,axiom,(
% 2.65/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.65/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 2.65/0.75  fof(f1028,plain,(
% 2.65/0.75    ~sP5(sK4(sK2,k1_xboole_0),sK2)),
% 2.65/0.75    inference(backward_demodulation,[],[f789,f887])).
% 2.65/0.75  fof(f1027,plain,(
% 2.65/0.75    r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)),
% 2.65/0.75    inference(backward_demodulation,[],[f788,f887])).
% 2.65/0.75  % SZS output end Proof for theBenchmark
% 2.65/0.75  % (5189)------------------------------
% 2.65/0.75  % (5189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.75  % (5189)Termination reason: Refutation
% 2.65/0.75  
% 2.65/0.75  % (5189)Memory used [KB]: 7803
% 2.65/0.75  % (5189)Time elapsed: 0.299 s
% 2.65/0.75  % (5189)------------------------------
% 2.65/0.75  % (5189)------------------------------
% 2.65/0.75  % (5164)Success in time 0.386 s
%------------------------------------------------------------------------------
