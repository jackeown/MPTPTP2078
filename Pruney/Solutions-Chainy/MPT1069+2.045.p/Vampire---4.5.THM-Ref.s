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
% DateTime   : Thu Dec  3 13:07:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 249 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  320 (1513 expanded)
%              Number of equality atoms :   74 ( 312 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f42])).

% (3040)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (3032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f161,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f157])).

fof(f157,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f154,f142])).

fof(f142,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f141,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f141,plain,
    ( k1_xboole_0 = sK2
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f139,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (3028)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f139,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f138,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f114,f101])).

fof(f101,plain,(
    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4))) ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f33,f79])).

fof(f79,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X1))
      | v1_xboole_0(sK1)
      | k1_xboole_0 = sK2
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f112,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f112,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f110,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
      | k1_xboole_0 = sK2
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f138,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_xboole_0(k1_relat_1(sK4))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f132,f125])).

fof(f125,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f115,f101])).

fof(f115,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X2))
      | v1_xboole_0(sK1)
      | k1_xboole_0 = sK2
      | m1_subset_1(k1_funct_1(sK3,sK5),X2) ) ),
    inference(resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)
      | v1_xboole_0(k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f130,f37])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0)
      | ~ m1_subset_1(X0,k1_relat_1(sK4))
      | v1_xboole_0(k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f120,f44])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f49,plain,(
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

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f59,plain,(
    ! [X8,X7] :
      ( ~ v5_relat_1(sK4,X7)
      | ~ v1_relat_1(sK4)
      | ~ r2_hidden(X8,k1_relat_1(sK4))
      | k7_partfun1(X7,sK4,X8) = k1_funct_1(sK4,X8) ) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f35,f153])).

fof(f153,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f151,f32])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) ) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) ) ),
    inference(subsumption_resolution,[],[f148,f88])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) ) ),
    inference(superposition,[],[f135,f79])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
      | ~ m1_subset_1(X1,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ) ),
    inference(resolution,[],[f75,f36])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(X3,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1))
      | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f74,f34])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(X3,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(X3,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f72,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(X3,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(X3,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3)) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f35,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (3031)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3039)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (3035)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (3027)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3027)Refutation not found, incomplete strategy% (3027)------------------------------
% 0.21/0.49  % (3027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3027)Memory used [KB]: 10618
% 0.21/0.49  % (3027)Time elapsed: 0.063 s
% 0.21/0.49  % (3027)------------------------------
% 0.21/0.49  % (3027)------------------------------
% 0.21/0.49  % (3039)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f161,f42])).
% 0.21/0.50  % (3040)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (3032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f41,f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(superposition,[],[f154,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(resolution,[],[f139,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  % (3028)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | k1_xboole_0 = sK2 | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_relat_1(sK4)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f114,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4)))),
% 0.21/0.51    inference(resolution,[],[f88,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.51    inference(backward_demodulation,[],[f33,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.51    inference(resolution,[],[f37,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X1)) | v1_xboole_0(sK1) | k1_xboole_0 = sK2 | ~v1_xboole_0(X1)) )),
% 0.21/0.51    inference(resolution,[],[f112,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f110,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f71,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.51    inference(resolution,[],[f39,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | v1_xboole_0(k1_relat_1(sK4)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f132,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f115,f101])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X2] : (~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X2)) | v1_xboole_0(sK1) | k1_xboole_0 = sK2 | m1_subset_1(k1_funct_1(sK3,sK5),X2)) )),
% 0.21/0.51    inference(resolution,[],[f112,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) | v1_xboole_0(k1_relat_1(sK4))) )),
% 0.21/0.51    inference(resolution,[],[f130,f37])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0) | ~m1_subset_1(X0,k1_relat_1(sK4)) | v1_xboole_0(k1_relat_1(sK4))) )),
% 0.21/0.51    inference(resolution,[],[f120,f44])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(X1,sK4,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.51    inference(resolution,[],[f59,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X8,X7] : (~v5_relat_1(sK4,X7) | ~v1_relat_1(sK4) | ~r2_hidden(X8,k1_relat_1(sK4)) | k7_partfun1(X7,sK4,X8) = k1_funct_1(sK4,X8)) )),
% 0.21/0.51    inference(resolution,[],[f36,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(backward_demodulation,[],[f35,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(resolution,[],[f151,f32])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f37])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f88])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0)) )),
% 0.21/0.51    inference(superposition,[],[f135,f79])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) | ~m1_subset_1(X1,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1))) )),
% 0.21/0.51    inference(resolution,[],[f75,f36])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(X3,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1)) | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f34])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(X3,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f40])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(X3,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f38])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(X3,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f41])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (v1_xboole_0(sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(X3,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X2,X1)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X2,sK3,X1),X3) = k1_funct_1(X1,k1_funct_1(sK3,X3))) )),
% 0.21/0.51    inference(resolution,[],[f39,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3039)------------------------------
% 0.21/0.51  % (3039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3039)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3039)Memory used [KB]: 1663
% 0.21/0.51  % (3039)Time elapsed: 0.068 s
% 0.21/0.51  % (3039)------------------------------
% 0.21/0.51  % (3039)------------------------------
% 0.21/0.51  % (3025)Success in time 0.152 s
%------------------------------------------------------------------------------
