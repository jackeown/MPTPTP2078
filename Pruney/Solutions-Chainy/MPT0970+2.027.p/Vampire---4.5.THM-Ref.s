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
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 (3543 expanded)
%              Number of leaves         :    9 ( 656 expanded)
%              Depth                    :   28
%              Number of atoms          :  250 (16770 expanded)
%              Number of equality atoms :   92 (5024 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f710,plain,(
    $false ),
    inference(resolution,[],[f697,f411])).

fof(f411,plain,(
    r2_hidden(sK3(sK8(k1_xboole_0,sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f307,f404])).

fof(f404,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f401,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f401,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f311,f343])).

fof(f343,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f336,f299])).

fof(f299,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f26,f294])).

fof(f294,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f291,f111])).

fof(f111,plain,(
    r2_hidden(sK3(sK8(sK1,sK2)),sK0) ),
    inference(resolution,[],[f22,f82])).

fof(f82,plain,(
    r2_hidden(sK8(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f27,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

% (11612)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f79,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK8(sK1,sK2),sK1) ),
    inference(resolution,[],[f26,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK8(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f22,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f291,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(sK8(sK1,sK2)),X7)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f290,f138])).

fof(f138,plain,(
    ! [X0] : ~ r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f136,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f26,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f83,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK8(sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f80,plain,(
    ! [X0] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X0,sK8(sK1,sK2)),sK2) ) ),
    inference(resolution,[],[f26,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X4,sK8(X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f21])).

% (11616)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f290,plain,(
    ! [X7] :
      ( r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X7))
      | ~ r2_hidden(sK3(sK8(sK1,sK2)),X7)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f282,f128])).

fof(f128,plain,(
    sK8(sK1,sK2) = k1_funct_1(sK2,sK3(sK8(sK1,sK2))) ),
    inference(resolution,[],[f23,f82])).

fof(f23,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f282,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(sK8(sK1,sK2)),X7)
      | r2_hidden(k1_funct_1(sK2,sK3(sK8(sK1,sK2))),k9_relat_1(sK2,X7))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f263,f111])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k1_funct_1(sK2,X0),k9_relat_1(sK2,X1))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f258,f74])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k1_funct_1(sK2,X0),k9_relat_1(sK2,X1))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f68,f144])).

fof(f144,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f73,f75])).

fof(f75,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f26,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f72,f26])).

fof(f72,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f25,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f25,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X9,X10)
      | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10)) ) ),
    inference(resolution,[],[f24,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f336,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f298,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f298,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f294])).

fof(f311,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f132,f294])).

fof(f132,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f27,f76])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f307,plain,(
    r2_hidden(sK3(sK8(k1_xboole_0,sK2)),sK0) ),
    inference(backward_demodulation,[],[f111,f294])).

fof(f697,plain,(
    ! [X7] : ~ r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7) ),
    inference(subsumption_resolution,[],[f696,f312])).

fof(f312,plain,(
    ! [X0] : ~ r2_hidden(sK8(k1_xboole_0,sK2),k9_relat_1(sK2,X0)) ),
    inference(backward_demodulation,[],[f138,f294])).

fof(f696,plain,(
    ! [X7] :
      ( r2_hidden(sK8(k1_xboole_0,sK2),k9_relat_1(sK2,X7))
      | ~ r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7) ) ),
    inference(forward_demodulation,[],[f676,f310])).

fof(f310,plain,(
    sK8(k1_xboole_0,sK2) = k1_funct_1(sK2,sK3(sK8(k1_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f128,f294])).

fof(f676,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7)
      | r2_hidden(k1_funct_1(sK2,sK3(sK8(k1_xboole_0,sK2))),k9_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f442,f411])).

fof(f442,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ r2_hidden(X9,X10)
      | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10)) ) ),
    inference(subsumption_resolution,[],[f431,f74])).

fof(f431,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X9,X10)
      | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10)) ) ),
    inference(backward_demodulation,[],[f68,f428])).

fof(f428,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f409,f427])).

fof(f427,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f419,f407])).

fof(f407,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f299,f404])).

fof(f419,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f406,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f406,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f298,f404])).

fof(f409,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f301,f404])).

fof(f301,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f75,f294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11619)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (11625)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (11617)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (11622)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (11622)Refutation not found, incomplete strategy% (11622)------------------------------
% 0.21/0.48  % (11622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (11622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (11622)Memory used [KB]: 10618
% 0.21/0.48  % (11622)Time elapsed: 0.072 s
% 0.21/0.48  % (11622)------------------------------
% 0.21/0.48  % (11622)------------------------------
% 0.21/0.48  % (11630)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (11618)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (11625)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (11620)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f710,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f697,f411])).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    r2_hidden(sK3(sK8(k1_xboole_0,sK2)),k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f307,f404])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f401,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f311,f343])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f336,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f26,f294])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(resolution,[],[f291,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r2_hidden(sK3(sK8(sK1,sK2)),sK0)),
% 0.21/0.49    inference(resolution,[],[f22,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    r2_hidden(sK8(sK1,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % (11612)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK8(sK1,sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f26,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ( ! [X7] : (~r2_hidden(sK3(sK8(sK1,sK2)),X7) | k1_xboole_0 = sK1) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f290,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f26,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(resolution,[],[f83,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK8(sK1,sK2)),sK2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f27])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X0,sK8(sK1,sK2)),sK2)) )),
% 0.21/0.49    inference(resolution,[],[f26,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X4,sK8(X1,X2)),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  % (11616)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X7] : (r2_hidden(sK8(sK1,sK2),k9_relat_1(sK2,X7)) | ~r2_hidden(sK3(sK8(sK1,sK2)),X7) | k1_xboole_0 = sK1) )),
% 0.21/0.49    inference(forward_demodulation,[],[f282,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    sK8(sK1,sK2) = k1_funct_1(sK2,sK3(sK8(sK1,sK2)))),
% 0.21/0.49    inference(resolution,[],[f23,f82])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X7] : (~r2_hidden(sK3(sK8(sK1,sK2)),X7) | r2_hidden(k1_funct_1(sK2,sK3(sK8(sK1,sK2))),k9_relat_1(sK2,X7)) | k1_xboole_0 = sK1) )),
% 0.21/0.49    inference(resolution,[],[f263,f111])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK2,X0),k9_relat_1(sK2,X1)) | k1_xboole_0 = sK1) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f74])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK2) | ~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK2,X0),k9_relat_1(sK2,X1)) | k1_xboole_0 = sK1) )),
% 0.21/0.49    inference(superposition,[],[f68,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(superposition,[],[f73,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f26,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f26])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f25,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X10,X9] : (~r2_hidden(X9,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X9,X10) | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10))) )),
% 0.21/0.49    inference(resolution,[],[f24,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | r2_hidden(k1_funct_1(X0,X4),X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | k1_funct_1(X0,X4) != X3 | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.21/0.49    inference(resolution,[],[f298,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f25,f294])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f132,f294])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    sK1 != k2_relat_1(sK2)),
% 0.21/0.49    inference(superposition,[],[f27,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f26,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    r2_hidden(sK3(sK8(k1_xboole_0,sK2)),sK0)),
% 0.21/0.49    inference(backward_demodulation,[],[f111,f294])).
% 0.21/0.49  fof(f697,plain,(
% 0.21/0.49    ( ! [X7] : (~r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f696,f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK8(k1_xboole_0,sK2),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f138,f294])).
% 0.21/0.49  fof(f696,plain,(
% 0.21/0.49    ( ! [X7] : (r2_hidden(sK8(k1_xboole_0,sK2),k9_relat_1(sK2,X7)) | ~r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f676,f310])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    sK8(k1_xboole_0,sK2) = k1_funct_1(sK2,sK3(sK8(k1_xboole_0,sK2)))),
% 0.21/0.49    inference(backward_demodulation,[],[f128,f294])).
% 0.21/0.49  fof(f676,plain,(
% 0.21/0.49    ( ! [X7] : (~r2_hidden(sK3(sK8(k1_xboole_0,sK2)),X7) | r2_hidden(k1_funct_1(sK2,sK3(sK8(k1_xboole_0,sK2))),k9_relat_1(sK2,X7))) )),
% 0.21/0.49    inference(resolution,[],[f442,f411])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    ( ! [X10,X9] : (~r2_hidden(X9,k1_xboole_0) | ~r2_hidden(X9,X10) | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f431,f74])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ( ! [X10,X9] : (~r2_hidden(X9,k1_xboole_0) | ~v1_relat_1(sK2) | ~r2_hidden(X9,X10) | r2_hidden(k1_funct_1(sK2,X9),k9_relat_1(sK2,X10))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f428])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f409,f427])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f419,f407])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f299,f404])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.49    inference(resolution,[],[f406,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f406,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f298,f404])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f301,f404])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f75,f294])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11625)------------------------------
% 0.21/0.49  % (11625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11625)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11625)Memory used [KB]: 1918
% 0.21/0.49  % (11625)Time elapsed: 0.021 s
% 0.21/0.49  % (11625)------------------------------
% 0.21/0.49  % (11625)------------------------------
% 0.21/0.49  % (11607)Success in time 0.135 s
%------------------------------------------------------------------------------
