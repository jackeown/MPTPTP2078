%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 707 expanded)
%              Number of leaves         :   12 ( 136 expanded)
%              Depth                    :   23
%              Number of atoms          :  302 (3921 expanded)
%              Number of equality atoms :  114 ( 882 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(resolution,[],[f512,f143])).

fof(f143,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f512,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f451,f498])).

fof(f498,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f35,f410,f233])).

fof(f233,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,sK5(X4,k1_xboole_0))
      | ~ r1_tarski(X4,X5)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,k1_xboole_0),X1)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f158,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f158,plain,(
    ! [X5] :
      ( r2_hidden(sK5(X5,k1_xboole_0),X5)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f38,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f35,f48])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f410,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f391,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f391,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f75,f384])).

fof(f384,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f142,f363])).

fof(f363,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f31,f356])).

fof(f356,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f350,f328])).

fof(f328,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f32,f95,f327])).

fof(f327,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f326])).

fof(f326,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f302,f274])).

% (11271)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (11289)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f274,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f33,f273])).

fof(f273,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f265,f177])).

fof(f177,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f265,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f56,f34])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f33,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f302,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(global_subsumption,[],[f28,f94,f296])).

fof(f296,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),sK0)
      | sK3 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f36,f272])).

fof(f272,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f29,f271])).

fof(f271,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(forward_demodulation,[],[f264,f176])).

fof(f176,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f30,f50])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

% (11280)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f264,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f56,f30])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

% (11283)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

% (11285)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f34,f49])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f350,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f274,f349])).

fof(f349,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ r2_hidden(sK4(sK3,sK2),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f347,f272])).

fof(f347,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(global_subsumption,[],[f32,f95,f346])).

fof(f346,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(equality_resolution,[],[f318])).

fof(f318,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(global_subsumption,[],[f28,f94,f314])).

fof(f314,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(superposition,[],[f37,f27])).

fof(f27,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f142,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f34,f67])).

fof(f75,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f451,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f387,f439])).

fof(f439,plain,(
    k1_xboole_0 = sK3 ),
    inference(unit_resulting_resolution,[],[f35,f409,f233])).

fof(f409,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f390,f59])).

fof(f390,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f74,f384])).

fof(f74,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f44])).

fof(f387,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f31,f384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (11270)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (11262)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (11278)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (11277)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (11286)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (11266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (11286)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (11263)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (11284)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (11276)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (11291)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (11288)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (11282)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (11265)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (11264)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (11267)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (11268)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (11287)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (11274)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f541,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f512,f143])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f73,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.54    inference(equality_resolution,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f35,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f512,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f451,f498])).
% 0.22/0.54  fof(f498,plain,(
% 0.22/0.54    k1_xboole_0 = sK2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f35,f410,f233])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ( ! [X4,X5] : (~r1_tarski(X5,sK5(X4,k1_xboole_0)) | ~r1_tarski(X4,X5) | k1_xboole_0 = X4) )),
% 0.22/0.54    inference(resolution,[],[f161,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,k1_xboole_0),X1) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f158,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X5] : (r2_hidden(sK5(X5,k1_xboole_0),X5) | k1_xboole_0 = X5) )),
% 0.22/0.54    inference(resolution,[],[f38,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f35,f48])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    r1_tarski(sK2,k1_xboole_0)),
% 0.22/0.54    inference(forward_demodulation,[],[f391,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f391,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 0.22/0.54    inference(backward_demodulation,[],[f75,f384])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    k1_xboole_0 = sK1),
% 0.22/0.55    inference(global_subsumption,[],[f142,f363])).
% 0.22/0.55  fof(f363,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(superposition,[],[f31,f356])).
% 0.22/0.55  fof(f356,plain,(
% 0.22/0.55    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f351])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    sK2 = sK3 | k1_xboole_0 = sK1 | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(resolution,[],[f350,f328])).
% 0.22/0.55  fof(f328,plain,(
% 0.22/0.55    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(global_subsumption,[],[f32,f95,f327])).
% 0.22/0.55  fof(f327,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f326])).
% 0.22/0.55  fof(f326,plain,(
% 0.22/0.55    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f325])).
% 0.22/0.55  fof(f325,plain,(
% 0.22/0.55    sK0 != sK0 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(superposition,[],[f302,f274])).
% 0.22/0.55  % (11271)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (11289)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  fof(f274,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(global_subsumption,[],[f33,f273])).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f265,f177])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f34,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.55    inference(negated_conjecture,[],[f12])).
% 0.22/0.55  fof(f12,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(resolution,[],[f56,f34])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f302,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.55    inference(global_subsumption,[],[f28,f94,f296])).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.55    inference(superposition,[],[f36,f272])).
% 0.22/0.55  fof(f272,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(global_subsumption,[],[f29,f271])).
% 0.22/0.55  fof(f271,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(forward_demodulation,[],[f264,f176])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f30,f50])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  % (11280)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(resolution,[],[f56,f30])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  % (11283)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.55  % (11285)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f30,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f34,f49])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 0.22/0.55    inference(global_subsumption,[],[f274,f349])).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    sK0 != k1_relat_1(sK2) | sK2 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(superposition,[],[f347,f272])).
% 0.22/0.55  fof(f347,plain,(
% 0.22/0.55    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 0.22/0.55    inference(global_subsumption,[],[f32,f95,f346])).
% 0.22/0.55  fof(f346,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 0.22/0.55    inference(equality_resolution,[],[f318])).
% 0.22/0.55  fof(f318,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK2,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 0.22/0.55    inference(global_subsumption,[],[f28,f94,f314])).
% 0.22/0.55  fof(f314,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK2,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 0.22/0.55    inference(superposition,[],[f37,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f34,f67])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f34,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f451,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f387,f439])).
% 0.22/0.55  fof(f439,plain,(
% 0.22/0.55    k1_xboole_0 = sK3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f35,f409,f233])).
% 0.22/0.55  fof(f409,plain,(
% 0.22/0.55    r1_tarski(sK3,k1_xboole_0)),
% 0.22/0.55    inference(forward_demodulation,[],[f390,f59])).
% 0.22/0.55  fof(f390,plain,(
% 0.22/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))),
% 0.22/0.55    inference(backward_demodulation,[],[f74,f384])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f30,f44])).
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.22/0.55    inference(backward_demodulation,[],[f31,f384])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11286)------------------------------
% 0.22/0.55  % (11286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11286)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11286)Memory used [KB]: 6524
% 0.22/0.55  % (11286)Time elapsed: 0.123 s
% 0.22/0.55  % (11286)------------------------------
% 0.22/0.55  % (11286)------------------------------
% 0.22/0.55  % (11261)Success in time 0.189 s
%------------------------------------------------------------------------------
