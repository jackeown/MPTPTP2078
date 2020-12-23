%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:26 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 227 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  232 ( 875 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f762,plain,(
    $false ),
    inference(subsumption_resolution,[],[f667,f94])).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f92,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f667,plain,(
    r2_hidden(sK11(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f220,f641])).

fof(f641,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f610,f156])).

fof(f156,plain,(
    ~ r2_hidden(sK9(sK4,sK2,sK3),sK0) ),
    inference(resolution,[],[f155,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f155,plain,(
    ~ m1_subset_1(sK9(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f154,f140])).

fof(f140,plain,(
    r2_hidden(sK9(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f136,f82])).

fof(f82,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( r2_hidden(sK9(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f133,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f133,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f32,f129])).

fof(f129,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f63,f35])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f32,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f154,plain,
    ( ~ r2_hidden(sK9(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK9(sK4,sK2,sK3),sK0) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK9(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK9(sK4,sK2,sK3),sK0) ),
    inference(superposition,[],[f31,f152])).

fof(f152,plain,(
    sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f151,f82])).

fof(f151,plain,
    ( sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f148,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f148,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f138,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f138,plain,(
    r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f134,f82])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f610,plain,
    ( r2_hidden(sK9(sK4,sK2,sK3),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f139,f608])).

fof(f608,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f607,f115])).

fof(f115,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f607,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f604,f34])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f604,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (3202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (3177)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (3176)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (3195)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (3196)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (3193)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (3201)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f139,plain,(
    r2_hidden(sK9(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f135,f82])).

fof(f135,plain,
    ( r2_hidden(sK9(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f133,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f220,plain,(
    r2_hidden(sK11(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK0,sK1),sK1) ),
    inference(resolution,[],[f215,f160])).

fof(f160,plain,(
    r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f150,f76])).

fof(f76,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),X0) ) ),
    inference(resolution,[],[f138,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(sK11(X0,X1,X2),X2) ) ),
    inference(resolution,[],[f171,f81])).

fof(f171,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
      | r2_hidden(sK11(X1,X3,X4),X4)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f66,f45])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | r2_hidden(sK11(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.53  % (3181)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (3197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.55  % (3189)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.55  % (3190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.55  % (3182)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.57  % (3183)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.57  % (3198)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.57  % (3180)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.57  % (3203)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.58  % (3175)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.58  % (3184)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.58  % (3192)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.58  % (3197)Refutation not found, incomplete strategy% (3197)------------------------------
% 1.48/0.58  % (3197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (3197)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (3197)Memory used [KB]: 10874
% 1.48/0.58  % (3197)Time elapsed: 0.143 s
% 1.48/0.58  % (3197)------------------------------
% 1.48/0.58  % (3197)------------------------------
% 1.48/0.58  % (3200)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.58  % (3191)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.58  % (3187)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.58  % (3194)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.59  % (3192)Refutation not found, incomplete strategy% (3192)------------------------------
% 1.48/0.59  % (3192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (3179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.48/0.59  % (3178)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.59  % (3185)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.59  % (3199)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.59  % (3192)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.59  
% 1.48/0.59  % (3192)Memory used [KB]: 10746
% 1.48/0.59  % (3192)Time elapsed: 0.115 s
% 1.48/0.59  % (3192)------------------------------
% 1.48/0.59  % (3192)------------------------------
% 1.48/0.59  % (3186)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.59  % (3181)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.60  % (3186)Refutation not found, incomplete strategy% (3186)------------------------------
% 1.48/0.60  % (3186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.60  % (3186)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.60  
% 1.48/0.60  % (3186)Memory used [KB]: 10746
% 1.48/0.60  % (3186)Time elapsed: 0.176 s
% 1.48/0.60  % (3186)------------------------------
% 1.48/0.60  % (3186)------------------------------
% 1.48/0.60  % SZS output start Proof for theBenchmark
% 1.48/0.60  fof(f762,plain,(
% 1.48/0.60    $false),
% 1.48/0.60    inference(subsumption_resolution,[],[f667,f94])).
% 1.48/0.60  fof(f94,plain,(
% 1.48/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.48/0.60    inference(resolution,[],[f92,f81])).
% 1.48/0.60  fof(f81,plain,(
% 1.48/0.60    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.48/0.60    inference(duplicate_literal_removal,[],[f80])).
% 1.48/0.60  fof(f80,plain,(
% 1.48/0.60    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.48/0.60    inference(resolution,[],[f40,f39])).
% 1.48/0.60  fof(f39,plain,(
% 1.48/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f19])).
% 1.48/0.60  fof(f19,plain,(
% 1.48/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.60    inference(ennf_transformation,[],[f1])).
% 1.48/0.60  fof(f1,axiom,(
% 1.48/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.60  fof(f40,plain,(
% 1.48/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f19])).
% 1.48/0.60  fof(f92,plain,(
% 1.48/0.60    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.48/0.60    inference(resolution,[],[f91,f45])).
% 1.48/0.60  fof(f45,plain,(
% 1.48/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f4])).
% 1.48/0.60  fof(f4,axiom,(
% 1.48/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.60  fof(f91,plain,(
% 1.48/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.48/0.60    inference(resolution,[],[f62,f36])).
% 1.48/0.60  fof(f36,plain,(
% 1.48/0.60    v1_xboole_0(k1_xboole_0)),
% 1.48/0.60    inference(cnf_transformation,[],[f2])).
% 1.48/0.60  fof(f2,axiom,(
% 1.48/0.60    v1_xboole_0(k1_xboole_0)),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.60  fof(f62,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f27])).
% 1.48/0.60  fof(f27,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.48/0.60    inference(ennf_transformation,[],[f5])).
% 1.48/0.60  fof(f5,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.48/0.60  fof(f667,plain,(
% 1.48/0.60    r2_hidden(sK11(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK0,k1_xboole_0),k1_xboole_0)),
% 1.48/0.60    inference(backward_demodulation,[],[f220,f641])).
% 1.48/0.60  fof(f641,plain,(
% 1.48/0.60    k1_xboole_0 = sK1),
% 1.48/0.60    inference(subsumption_resolution,[],[f610,f156])).
% 1.48/0.60  fof(f156,plain,(
% 1.48/0.60    ~r2_hidden(sK9(sK4,sK2,sK3),sK0)),
% 1.48/0.60    inference(resolution,[],[f155,f37])).
% 1.48/0.60  fof(f37,plain,(
% 1.48/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f18])).
% 1.48/0.60  fof(f18,plain,(
% 1.48/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.48/0.60    inference(ennf_transformation,[],[f3])).
% 1.48/0.60  fof(f3,axiom,(
% 1.48/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.48/0.60  fof(f155,plain,(
% 1.48/0.60    ~m1_subset_1(sK9(sK4,sK2,sK3),sK0)),
% 1.48/0.60    inference(subsumption_resolution,[],[f154,f140])).
% 1.48/0.60  fof(f140,plain,(
% 1.48/0.60    r2_hidden(sK9(sK4,sK2,sK3),sK2)),
% 1.48/0.60    inference(subsumption_resolution,[],[f136,f82])).
% 1.48/0.60  fof(f82,plain,(
% 1.48/0.60    v1_relat_1(sK3)),
% 1.48/0.60    inference(resolution,[],[f51,f35])).
% 1.48/0.60  fof(f35,plain,(
% 1.48/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.60    inference(cnf_transformation,[],[f17])).
% 1.48/0.60  fof(f17,plain,(
% 1.48/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.48/0.60    inference(flattening,[],[f16])).
% 1.48/0.60  fof(f16,plain,(
% 1.48/0.60    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.48/0.60    inference(ennf_transformation,[],[f15])).
% 1.48/0.60  fof(f15,negated_conjecture,(
% 1.48/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.48/0.60    inference(negated_conjecture,[],[f14])).
% 1.48/0.60  fof(f14,conjecture,(
% 1.48/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 1.48/0.60  fof(f51,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f21])).
% 1.48/0.60  fof(f21,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(ennf_transformation,[],[f9])).
% 1.48/0.60  fof(f9,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.60  fof(f136,plain,(
% 1.48/0.60    r2_hidden(sK9(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.48/0.60    inference(resolution,[],[f133,f49])).
% 1.48/0.60  fof(f49,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f20])).
% 1.48/0.60  fof(f20,plain,(
% 1.48/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.48/0.60    inference(ennf_transformation,[],[f7])).
% 1.48/0.60  fof(f7,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.48/0.60  fof(f133,plain,(
% 1.48/0.60    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.48/0.60    inference(backward_demodulation,[],[f32,f129])).
% 1.48/0.60  fof(f129,plain,(
% 1.48/0.60    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.48/0.60    inference(resolution,[],[f63,f35])).
% 1.48/0.60  fof(f63,plain,(
% 1.48/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f28])).
% 1.48/0.60  fof(f28,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(ennf_transformation,[],[f11])).
% 1.48/0.60  fof(f11,axiom,(
% 1.48/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.48/0.60  fof(f32,plain,(
% 1.48/0.60    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.48/0.60    inference(cnf_transformation,[],[f17])).
% 1.48/0.60  fof(f154,plain,(
% 1.48/0.60    ~r2_hidden(sK9(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK9(sK4,sK2,sK3),sK0)),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f153])).
% 1.48/0.60  fof(f153,plain,(
% 1.48/0.60    sK4 != sK4 | ~r2_hidden(sK9(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK9(sK4,sK2,sK3),sK0)),
% 1.48/0.60    inference(superposition,[],[f31,f152])).
% 1.48/0.60  fof(f152,plain,(
% 1.48/0.60    sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3))),
% 1.48/0.60    inference(subsumption_resolution,[],[f151,f82])).
% 1.48/0.60  fof(f151,plain,(
% 1.48/0.60    sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.48/0.60    inference(subsumption_resolution,[],[f148,f33])).
% 1.48/0.60  fof(f33,plain,(
% 1.48/0.60    v1_funct_1(sK3)),
% 1.48/0.60    inference(cnf_transformation,[],[f17])).
% 1.48/0.60  fof(f148,plain,(
% 1.48/0.60    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK9(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.48/0.60    inference(resolution,[],[f138,f60])).
% 1.48/0.60  fof(f60,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f26])).
% 1.48/0.60  fof(f26,plain,(
% 1.48/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.60    inference(flattening,[],[f25])).
% 1.48/0.60  fof(f25,plain,(
% 1.48/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.48/0.60    inference(ennf_transformation,[],[f8])).
% 1.48/0.60  fof(f8,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.48/0.60  fof(f138,plain,(
% 1.48/0.60    r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK3)),
% 1.48/0.60    inference(subsumption_resolution,[],[f134,f82])).
% 1.48/0.60  fof(f134,plain,(
% 1.48/0.60    r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.48/0.60    inference(resolution,[],[f133,f48])).
% 1.48/0.60  fof(f48,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f20])).
% 1.48/0.60  fof(f31,plain,(
% 1.48/0.60    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f17])).
% 1.48/0.60  fof(f610,plain,(
% 1.48/0.60    r2_hidden(sK9(sK4,sK2,sK3),sK0) | k1_xboole_0 = sK1),
% 1.48/0.60    inference(superposition,[],[f139,f608])).
% 1.48/0.60  fof(f608,plain,(
% 1.48/0.60    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.48/0.60    inference(superposition,[],[f607,f115])).
% 1.48/0.60  fof(f115,plain,(
% 1.48/0.60    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.48/0.60    inference(resolution,[],[f52,f35])).
% 1.48/0.60  fof(f52,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f22])).
% 1.48/0.60  fof(f22,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(ennf_transformation,[],[f10])).
% 1.48/0.60  fof(f10,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.48/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.60  fof(f607,plain,(
% 1.48/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.48/0.60    inference(subsumption_resolution,[],[f604,f34])).
% 1.48/0.60  fof(f34,plain,(
% 1.48/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.48/0.60    inference(cnf_transformation,[],[f17])).
% 1.48/0.60  fof(f604,plain,(
% 1.48/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 1.48/0.60    inference(resolution,[],[f58,f35])).
% 1.48/0.60  fof(f58,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f24])).
% 1.48/0.60  % (3202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.60  % (3177)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.60  % (3176)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.48/0.60  % (3195)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.60  % (3196)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.60  % (3193)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.60  % (3201)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.61  fof(f24,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(flattening,[],[f23])).
% 1.48/0.61  fof(f23,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.61    inference(ennf_transformation,[],[f13])).
% 1.48/0.61  fof(f13,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.48/0.61  fof(f139,plain,(
% 1.48/0.61    r2_hidden(sK9(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.48/0.61    inference(subsumption_resolution,[],[f135,f82])).
% 1.48/0.61  fof(f135,plain,(
% 1.48/0.61    r2_hidden(sK9(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.48/0.61    inference(resolution,[],[f133,f47])).
% 1.48/0.61  fof(f47,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f20])).
% 1.48/0.61  fof(f220,plain,(
% 1.48/0.61    r2_hidden(sK11(k4_tarski(sK9(sK4,sK2,sK3),sK4),sK0,sK1),sK1)),
% 1.48/0.61    inference(resolution,[],[f215,f160])).
% 1.48/0.61  fof(f160,plain,(
% 1.48/0.61    r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),k2_zfmisc_1(sK0,sK1))),
% 1.48/0.61    inference(resolution,[],[f150,f76])).
% 1.48/0.61  fof(f76,plain,(
% 1.48/0.61    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.48/0.61    inference(resolution,[],[f46,f35])).
% 1.48/0.61  fof(f46,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f4])).
% 1.48/0.61  fof(f150,plain,(
% 1.48/0.61    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(k4_tarski(sK9(sK4,sK2,sK3),sK4),X0)) )),
% 1.48/0.61    inference(resolution,[],[f138,f38])).
% 1.48/0.61  fof(f38,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f19])).
% 1.48/0.61  fof(f215,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK11(X0,X1,X2),X2)) )),
% 1.48/0.61    inference(resolution,[],[f171,f81])).
% 1.48/0.61  fof(f171,plain,(
% 1.48/0.61    ( ! [X4,X2,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X3,X4)) | r2_hidden(sK11(X1,X3,X4),X4) | ~r2_hidden(X1,X2)) )),
% 1.48/0.61    inference(resolution,[],[f66,f45])).
% 1.48/0.61  fof(f66,plain,(
% 1.48/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | r2_hidden(sK11(X0,X1,X2),X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f30])).
% 1.48/0.61  fof(f30,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.48/0.61    inference(flattening,[],[f29])).
% 1.48/0.61  fof(f29,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.48/0.61    inference(ennf_transformation,[],[f12])).
% 1.48/0.61  fof(f12,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.48/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 1.48/0.61  % SZS output end Proof for theBenchmark
% 1.48/0.61  % (3181)------------------------------
% 1.48/0.61  % (3181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (3181)Termination reason: Refutation
% 1.48/0.61  
% 1.48/0.61  % (3181)Memory used [KB]: 6908
% 1.48/0.61  % (3181)Time elapsed: 0.142 s
% 1.48/0.61  % (3181)------------------------------
% 1.48/0.61  % (3181)------------------------------
% 1.48/0.61  % (3188)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.61  % (3185)Refutation not found, incomplete strategy% (3185)------------------------------
% 1.48/0.61  % (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (3174)Success in time 0.243 s
%------------------------------------------------------------------------------
