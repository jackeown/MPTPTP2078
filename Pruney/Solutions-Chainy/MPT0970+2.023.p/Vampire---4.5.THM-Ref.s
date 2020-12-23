%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 (4233 expanded)
%              Number of leaves         :   11 ( 928 expanded)
%              Depth                    :   23
%              Number of atoms          :  237 (16509 expanded)
%              Number of equality atoms :   82 (4659 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(global_subsumption,[],[f473,f507])).

fof(f507,plain,(
    ~ r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f360,f505])).

fof(f505,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f469,f493])).

fof(f493,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f454,f455,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
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

fof(f455,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f325,f438])).

fof(f438,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f34,f424])).

fof(f424,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f349,f391])).

fof(f391,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f324,f386])).

fof(f386,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(resolution,[],[f325,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f324,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f321])).

fof(f321,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f175,f310])).

fof(f310,plain,
    ( ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f196,f303])).

fof(f303,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f30,f302])).

fof(f302,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f300,f128])).

fof(f128,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f300,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f196,plain,(
    ~ r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f165,f178,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | sP5(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f63,f28])).

fof(f28,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f178,plain,(
    ~ sP5(sK7(sK1,k2_relat_1(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f80,f29,f164,f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f164,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f161,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f161,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f145,f158,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f158,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f157,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f157,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f149,f142])).

fof(f142,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f149,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f145,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(global_subsumption,[],[f31,f144])).

fof(f144,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f32,f52])).

fof(f32,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f165,plain,(
    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f161,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f175,plain,(
    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f64,f64,f64,f64,f165,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X2),X4)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,sK1)
      | ~ r1_tarski(X1,X3)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0),X3)
      | ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f97,f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X1),X2)
      | ~ r2_hidden(X1,sK1)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f93,f45])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),X1)
      | ~ r1_tarski(sK0,X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f349,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f145,f321])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f325,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f321])).

fof(f454,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f324,f438])).

fof(f469,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f345,f438])).

fof(f345,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f128,f321])).

fof(f360,plain,(
    ~ r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f196,f321])).

fof(f473,plain,(
    r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f357,f438])).

fof(f357,plain,(
    r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),sK0) ),
    inference(backward_demodulation,[],[f175,f321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18100)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (18124)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (18106)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (18098)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18101)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (18099)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18097)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18106)Refutation not found, incomplete strategy% (18106)------------------------------
% 0.21/0.51  % (18106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18106)Memory used [KB]: 10618
% 0.21/0.51  % (18106)Time elapsed: 0.109 s
% 0.21/0.51  % (18106)------------------------------
% 0.21/0.51  % (18106)------------------------------
% 0.21/0.52  % (18109)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18102)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (18107)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18111)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (18114)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (18096)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (18125)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (18122)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (18123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (18121)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (18112)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (18116)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (18105)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (18112)Refutation not found, incomplete strategy% (18112)------------------------------
% 0.21/0.54  % (18112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18112)Memory used [KB]: 10618
% 0.21/0.54  % (18112)Time elapsed: 0.140 s
% 0.21/0.54  % (18112)------------------------------
% 0.21/0.54  % (18112)------------------------------
% 0.21/0.54  % (18104)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (18105)Refutation not found, incomplete strategy% (18105)------------------------------
% 0.21/0.54  % (18105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18105)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18105)Memory used [KB]: 10618
% 0.21/0.54  % (18105)Time elapsed: 0.140 s
% 0.21/0.54  % (18105)------------------------------
% 0.21/0.54  % (18105)------------------------------
% 0.21/0.55  % (18113)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (18095)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (18115)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (18117)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (18108)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (18110)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (18118)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (18103)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (18120)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f523,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(global_subsumption,[],[f473,f507])).
% 0.21/0.59  fof(f507,plain,(
% 0.21/0.59    ~r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f360,f505])).
% 0.21/0.59  fof(f505,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f469,f493])).
% 0.21/0.59  fof(f493,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f454,f455,f66])).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f57])).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(flattening,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.59  fof(f455,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.59    inference(backward_demodulation,[],[f325,f438])).
% 0.21/0.59  fof(f438,plain,(
% 0.21/0.59    k1_xboole_0 = sK0),
% 0.21/0.59    inference(global_subsumption,[],[f34,f424])).
% 0.21/0.59  fof(f424,plain,(
% 0.21/0.59    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.59    inference(superposition,[],[f349,f391])).
% 0.21/0.59  fof(f391,plain,(
% 0.21/0.59    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.59    inference(global_subsumption,[],[f324,f386])).
% 0.21/0.59  fof(f386,plain,(
% 0.21/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.59    inference(resolution,[],[f325,f68])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  fof(f324,plain,(
% 0.21/0.59    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f30,f321])).
% 0.21/0.59  fof(f321,plain,(
% 0.21/0.59    k1_xboole_0 = sK1),
% 0.21/0.59    inference(global_subsumption,[],[f175,f310])).
% 0.21/0.59  fof(f310,plain,(
% 0.21/0.59    ~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) | k1_xboole_0 = sK1),
% 0.21/0.59    inference(superposition,[],[f196,f303])).
% 0.21/0.59  fof(f303,plain,(
% 0.21/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.59    inference(global_subsumption,[],[f30,f302])).
% 0.21/0.59  fof(f302,plain,(
% 0.21/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.59    inference(forward_demodulation,[],[f300,f128])).
% 0.21/0.59  fof(f128,plain,(
% 0.21/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f31,f51])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.59    inference(flattening,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.59    inference(negated_conjecture,[],[f12])).
% 0.21/0.59  fof(f12,conjecture,(
% 0.21/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.59  fof(f300,plain,(
% 0.21/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.59    inference(resolution,[],[f59,f31])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  fof(f196,plain,(
% 0.21/0.59    ~r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f165,f178,f98])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(sK3(X0),k1_relat_1(sK2)) | sP5(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.59    inference(superposition,[],[f63,f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.21/0.59    inference(equality_resolution,[],[f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.59  fof(f178,plain,(
% 0.21/0.59    ~sP5(sK7(sK1,k2_relat_1(sK2)),sK2)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f80,f29,f164,f62])).
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP5(X2,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f17])).
% 0.21/0.59  fof(f164,plain,(
% 0.21/0.59    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f161,f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f161,plain,(
% 0.21/0.59    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f145,f158,f44])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f158,plain,(
% 0.21/0.59    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f157,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.59  fof(f157,plain,(
% 0.21/0.59    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.59    inference(forward_demodulation,[],[f149,f142])).
% 0.21/0.59  fof(f142,plain,(
% 0.21/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f31,f52])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.59  fof(f149,plain,(
% 0.21/0.59    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f31,f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.59  fof(f145,plain,(
% 0.21/0.59    sK1 != k2_relat_1(sK2)),
% 0.21/0.59    inference(global_subsumption,[],[f31,f144])).
% 0.21/0.59  fof(f144,plain,(
% 0.21/0.59    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.59    inference(superposition,[],[f32,f52])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    v1_funct_1(sK2)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    v1_relat_1(sK2)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f31,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.59  fof(f165,plain,(
% 0.21/0.59    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f161,f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f175,plain,(
% 0.21/0.59    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f64,f64,f64,f64,f165,f106])).
% 0.21/0.59  fof(f106,plain,(
% 0.21/0.59    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X2),X4) | ~r1_tarski(X0,X1) | ~r2_hidden(X2,sK1) | ~r1_tarski(X1,X3) | ~r1_tarski(sK0,X0) | ~r1_tarski(X3,X4)) )),
% 0.21/0.59    inference(resolution,[],[f101,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f101,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0),X3) | ~r1_tarski(sK0,X1) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,sK1) | ~r1_tarski(X2,X3)) )),
% 0.21/0.59    inference(resolution,[],[f97,f45])).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X1),X2) | ~r2_hidden(X1,sK1) | ~r1_tarski(sK0,X0) | ~r1_tarski(X0,X2)) )),
% 0.21/0.59    inference(resolution,[],[f93,f45])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0),X1) | ~r1_tarski(sK0,X1) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.59    inference(resolution,[],[f45,f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f15])).
% 0.21/0.59  fof(f349,plain,(
% 0.21/0.59    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f145,f321])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.59  fof(f325,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.59    inference(backward_demodulation,[],[f31,f321])).
% 0.21/0.59  fof(f454,plain,(
% 0.21/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f324,f438])).
% 0.21/0.59  fof(f469,plain,(
% 0.21/0.59    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f345,f438])).
% 0.21/0.59  fof(f345,plain,(
% 0.21/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f128,f321])).
% 0.21/0.59  fof(f360,plain,(
% 0.21/0.59    ~r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_relat_1(sK2))),
% 0.21/0.59    inference(backward_demodulation,[],[f196,f321])).
% 0.21/0.59  fof(f473,plain,(
% 0.21/0.59    r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f357,f438])).
% 0.21/0.59  fof(f357,plain,(
% 0.21/0.59    r2_hidden(sK3(sK7(k1_xboole_0,k2_relat_1(sK2))),sK0)),
% 0.21/0.59    inference(backward_demodulation,[],[f175,f321])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (18120)------------------------------
% 0.21/0.59  % (18120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (18120)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (18120)Memory used [KB]: 6780
% 0.21/0.59  % (18120)Time elapsed: 0.190 s
% 0.21/0.59  % (18120)------------------------------
% 0.21/0.59  % (18120)------------------------------
% 0.21/0.59  % (18094)Success in time 0.229 s
%------------------------------------------------------------------------------
