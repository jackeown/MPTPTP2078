%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:35 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 780 expanded)
%              Number of leaves         :   21 ( 190 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 (3582 expanded)
%              Number of equality atoms :  125 ( 949 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f525,plain,(
    $false ),
    inference(subsumption_resolution,[],[f524,f240])).

fof(f240,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f238,f226])).

fof(f226,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f225,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f225,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f207,f191])).

fof(f191,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f190,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f190,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) ),
    inference(subsumption_resolution,[],[f189,f118])).

fof(f118,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f112,f111])).

fof(f111,plain,(
    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    inference(resolution,[],[f106,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) )
    & sK1 = k1_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f43])).

% (12059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3) )
      & sK1 = k1_relset_1(sK1,sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f109,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f106,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f189,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0))))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f187,f117])).

fof(f117,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f113,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f113,plain,(
    ! [X1] : v1_funct_1(k3_xboole_0(sK3,X1)) ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | v1_funct_1(k3_xboole_0(sK3,X1)) ) ),
    inference(resolution,[],[f106,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_funct_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_grfunc_1)).

fof(f187,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f67,f60])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f207,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f79,f95])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f238,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f96,f196])).

fof(f196,plain,(
    ! [X0] : sP0(k1_xboole_0,k1_xboole_0,X0) ),
    inference(resolution,[],[f191,f146])).

fof(f146,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | sP0(k1_xboole_0,X3,X2) ) ),
    inference(superposition,[],[f84,f95])).

% (12070)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

% (12064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f96,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f524,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f494,f511])).

fof(f511,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f481,f60])).

fof(f481,plain,(
    k1_relat_1(k1_xboole_0) = sK1 ),
    inference(backward_demodulation,[],[f208,f471])).

fof(f471,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f470,f448])).

fof(f448,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f446,f125])).

fof(f125,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X0,X1) ),
    inference(superposition,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f446,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1))
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f445,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f445,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1)) ) ),
    inference(subsumption_resolution,[],[f444,f118])).

fof(f444,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f442,f117])).

fof(f442,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f87,f60])).

% (12061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f470,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK3
      | r2_hidden(sK5(sK4(k1_xboole_0,sK3),k1_xboole_0,X1),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f465,f332])).

fof(f332,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f329,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f329,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f57,f325])).

fof(f325,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f324,f103])).

fof(f103,plain,(
    ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f59,f57])).

fof(f59,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f324,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f322,f58])).

fof(f58,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f322,plain,
    ( sK1 != k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f82,f144])).

fof(f144,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f84,f57])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f465,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = sK3
      | r2_hidden(sK5(sK4(k1_xboole_0,sK3),k1_xboole_0,X1),k1_xboole_0) ) ),
    inference(superposition,[],[f460,f95])).

fof(f460,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k1_xboole_0 = sK3
      | r2_hidden(sK5(sK4(k1_xboole_0,sK3),X7,X8),X7) ) ),
    inference(resolution,[],[f289,f332])).

fof(f289,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = X1
      | r2_hidden(sK5(sK4(X0,X1),X2,X3),X2) ) ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X3)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f208,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f204,f58])).

fof(f204,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f79,f57])).

fof(f494,plain,(
    ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f328,f471])).

fof(f328,plain,(
    ~ v1_funct_2(sK3,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f103,f325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:51:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.17/0.51  % (12080)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.17/0.52  % (12054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (12055)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (12056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.52  % (12074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.52  % (12063)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.53  % (12065)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (12058)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.53  % (12074)Refutation not found, incomplete strategy% (12074)------------------------------
% 1.35/0.53  % (12074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (12074)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (12074)Memory used [KB]: 10746
% 1.35/0.53  % (12074)Time elapsed: 0.065 s
% 1.35/0.53  % (12074)------------------------------
% 1.35/0.53  % (12074)------------------------------
% 1.35/0.54  % (12050)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (12053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (12052)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.55  % (12069)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (12081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (12068)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (12075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (12060)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.55  % (12068)Refutation not found, incomplete strategy% (12068)------------------------------
% 1.35/0.55  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (12068)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (12068)Memory used [KB]: 10618
% 1.35/0.55  % (12068)Time elapsed: 0.137 s
% 1.35/0.55  % (12068)------------------------------
% 1.35/0.55  % (12068)------------------------------
% 1.35/0.55  % (12077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (12078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (12079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (12072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (12066)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (12051)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.56  % (12073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.56  % (12062)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.56  % (12058)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % SZS output start Proof for theBenchmark
% 1.35/0.56  fof(f525,plain,(
% 1.35/0.56    $false),
% 1.35/0.56    inference(subsumption_resolution,[],[f524,f240])).
% 1.35/0.56  fof(f240,plain,(
% 1.35/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f238,f226])).
% 1.35/0.56  fof(f226,plain,(
% 1.35/0.56    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.35/0.56    inference(forward_demodulation,[],[f225,f60])).
% 1.35/0.56  fof(f60,plain,(
% 1.35/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(cnf_transformation,[],[f8])).
% 1.35/0.56  fof(f8,axiom,(
% 1.35/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.35/0.56  fof(f225,plain,(
% 1.35/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.35/0.56    inference(resolution,[],[f207,f191])).
% 1.35/0.56  fof(f191,plain,(
% 1.35/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.35/0.56    inference(forward_demodulation,[],[f190,f95])).
% 1.35/0.56  fof(f95,plain,(
% 1.35/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.35/0.56    inference(equality_resolution,[],[f76])).
% 1.35/0.56  fof(f76,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f48])).
% 1.35/0.56  fof(f48,plain,(
% 1.35/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.35/0.56    inference(flattening,[],[f47])).
% 1.35/0.56  fof(f47,plain,(
% 1.35/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.35/0.56    inference(nnf_transformation,[],[f3])).
% 1.35/0.56  fof(f3,axiom,(
% 1.35/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.35/0.56  fof(f190,plain,(
% 1.35/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0))))),
% 1.35/0.56    inference(subsumption_resolution,[],[f189,f118])).
% 1.35/0.56  fof(f118,plain,(
% 1.35/0.56    v1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(superposition,[],[f112,f111])).
% 1.35/0.56  fof(f111,plain,(
% 1.35/0.56    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 1.35/0.56    inference(resolution,[],[f106,f64])).
% 1.35/0.56  fof(f64,plain,(
% 1.35/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f22])).
% 1.35/0.56  fof(f22,plain,(
% 1.35/0.56    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f6])).
% 1.35/0.56  fof(f6,axiom,(
% 1.35/0.56    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 1.35/0.56  fof(f106,plain,(
% 1.35/0.56    v1_relat_1(sK3)),
% 1.35/0.56    inference(resolution,[],[f78,f57])).
% 1.35/0.56  fof(f57,plain,(
% 1.35/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.35/0.56    inference(cnf_transformation,[],[f44])).
% 1.35/0.56  fof(f44,plain,(
% 1.35/0.56    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) & sK1 = k1_relset_1(sK1,sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f43])).
% 1.35/0.56  % (12059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.56  fof(f43,plain,(
% 1.35/0.56    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) & sK1 = k1_relset_1(sK1,sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f21,plain,(
% 1.35/0.56    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.35/0.56    inference(flattening,[],[f20])).
% 1.35/0.56  fof(f20,plain,(
% 1.35/0.56    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.35/0.56    inference(ennf_transformation,[],[f19])).
% 1.35/0.56  fof(f19,negated_conjecture,(
% 1.35/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.35/0.56    inference(negated_conjecture,[],[f18])).
% 1.35/0.56  fof(f18,conjecture,(
% 1.35/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 1.35/0.56  fof(f78,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f31])).
% 1.35/0.56  fof(f31,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(ennf_transformation,[],[f12])).
% 1.35/0.56  fof(f12,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.35/0.56  fof(f112,plain,(
% 1.35/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f109,f56])).
% 1.35/0.56  fof(f56,plain,(
% 1.35/0.56    v1_funct_1(sK3)),
% 1.35/0.56    inference(cnf_transformation,[],[f44])).
% 1.35/0.56  fof(f109,plain,(
% 1.35/0.56    ( ! [X0] : (~v1_funct_1(sK3) | v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.35/0.56    inference(resolution,[],[f106,f73])).
% 1.35/0.56  fof(f73,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f30])).
% 1.35/0.56  fof(f30,plain,(
% 1.35/0.56    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/0.56    inference(flattening,[],[f29])).
% 1.35/0.56  fof(f29,plain,(
% 1.35/0.56    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f9])).
% 1.35/0.56  fof(f9,axiom,(
% 1.35/0.56    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.35/0.56  fof(f189,plain,(
% 1.35/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) | ~v1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(subsumption_resolution,[],[f187,f117])).
% 1.35/0.56  fof(f117,plain,(
% 1.35/0.56    v1_funct_1(k1_xboole_0)),
% 1.35/0.56    inference(superposition,[],[f113,f62])).
% 1.35/0.56  fof(f62,plain,(
% 1.35/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f1])).
% 1.35/0.56  fof(f1,axiom,(
% 1.35/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.35/0.56  fof(f113,plain,(
% 1.35/0.56    ( ! [X1] : (v1_funct_1(k3_xboole_0(sK3,X1))) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f110,f56])).
% 1.35/0.56  fof(f110,plain,(
% 1.35/0.56    ( ! [X1] : (~v1_funct_1(sK3) | v1_funct_1(k3_xboole_0(sK3,X1))) )),
% 1.35/0.56    inference(resolution,[],[f106,f72])).
% 1.35/0.56  fof(f72,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k3_xboole_0(X0,X1))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f28])).
% 1.35/0.56  fof(f28,plain,(
% 1.35/0.56    ! [X0,X1] : (v1_funct_1(k3_xboole_0(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/0.56    inference(flattening,[],[f27])).
% 1.35/0.56  fof(f27,plain,(
% 1.35/0.56    ! [X0,X1] : (v1_funct_1(k3_xboole_0(X0,X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f16])).
% 1.35/0.56  fof(f16,axiom,(
% 1.35/0.56    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v1_funct_1(k3_xboole_0(X0,X1)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_grfunc_1)).
% 1.35/0.56  fof(f187,plain,(
% 1.35/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(superposition,[],[f67,f60])).
% 1.35/0.56  fof(f67,plain,(
% 1.35/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f24])).
% 1.35/0.56  fof(f24,plain,(
% 1.35/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/0.56    inference(flattening,[],[f23])).
% 1.35/0.56  fof(f23,plain,(
% 1.35/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f17])).
% 1.35/0.56  fof(f17,axiom,(
% 1.35/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.35/0.56  fof(f207,plain,(
% 1.35/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 1.35/0.56    inference(superposition,[],[f79,f95])).
% 1.35/0.56  fof(f79,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f32,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(ennf_transformation,[],[f13])).
% 1.35/0.56  fof(f13,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.35/0.56  fof(f238,plain,(
% 1.35/0.56    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.35/0.56    inference(resolution,[],[f96,f196])).
% 1.35/0.56  fof(f196,plain,(
% 1.35/0.56    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.35/0.56    inference(resolution,[],[f191,f146])).
% 1.35/0.56  fof(f146,plain,(
% 1.35/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_xboole_0,X3,X2)) )),
% 1.35/0.56    inference(superposition,[],[f84,f95])).
% 1.35/0.56  % (12070)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  fof(f84,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f51])).
% 1.35/0.56  % (12064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.56  fof(f51,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(nnf_transformation,[],[f42])).
% 1.35/0.56  fof(f42,plain,(
% 1.35/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(definition_folding,[],[f34,f41])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.35/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.35/0.56  fof(f34,plain,(
% 1.35/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(flattening,[],[f33])).
% 1.35/0.56  fof(f33,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.56    inference(ennf_transformation,[],[f15])).
% 1.35/0.56  fof(f15,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.35/0.56  fof(f96,plain,(
% 1.35/0.56    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2)) )),
% 1.35/0.56    inference(equality_resolution,[],[f83])).
% 1.35/0.56  fof(f83,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f50])).
% 1.35/0.56  fof(f50,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.35/0.56    inference(rectify,[],[f49])).
% 1.35/0.56  fof(f49,plain,(
% 1.35/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.35/0.56    inference(nnf_transformation,[],[f41])).
% 1.35/0.56  fof(f524,plain,(
% 1.35/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.35/0.56    inference(forward_demodulation,[],[f494,f511])).
% 1.35/0.56  fof(f511,plain,(
% 1.35/0.56    k1_xboole_0 = sK1),
% 1.35/0.56    inference(forward_demodulation,[],[f481,f60])).
% 1.35/0.56  fof(f481,plain,(
% 1.35/0.56    k1_relat_1(k1_xboole_0) = sK1),
% 1.35/0.56    inference(backward_demodulation,[],[f208,f471])).
% 1.35/0.56  fof(f471,plain,(
% 1.35/0.56    k1_xboole_0 = sK3),
% 1.35/0.56    inference(subsumption_resolution,[],[f470,f448])).
% 1.35/0.56  fof(f448,plain,(
% 1.35/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.35/0.56    inference(condensation,[],[f447])).
% 1.35/0.56  fof(f447,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f446,f125])).
% 1.35/0.56  fof(f125,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1)) )),
% 1.35/0.56    inference(superposition,[],[f68,f69])).
% 1.35/0.56  fof(f69,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f2])).
% 1.35/0.56  fof(f2,axiom,(
% 1.35/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.35/0.56  fof(f68,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f4])).
% 1.35/0.56  fof(f4,axiom,(
% 1.35/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.35/0.56  fof(f446,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1)) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.35/0.56    inference(forward_demodulation,[],[f445,f63])).
% 1.35/0.56  fof(f63,plain,(
% 1.35/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f7])).
% 1.35/0.56  fof(f7,axiom,(
% 1.35/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.35/0.56  fof(f445,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1))) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f444,f118])).
% 1.35/0.56  fof(f444,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f442,f117])).
% 1.35/0.56  fof(f442,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k9_relat_1(k1_xboole_0,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X1)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.35/0.56    inference(superposition,[],[f87,f60])).
% 1.35/0.56  % (12061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.56  fof(f87,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X1,k1_relat_1(X2)) | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f36])).
% 1.35/0.56  fof(f36,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.35/0.56    inference(flattening,[],[f35])).
% 1.35/0.56  fof(f35,plain,(
% 1.35/0.56    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.35/0.56    inference(ennf_transformation,[],[f10])).
% 1.35/0.56  fof(f10,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 1.35/0.56  fof(f470,plain,(
% 1.35/0.56    ( ! [X1] : (k1_xboole_0 = sK3 | r2_hidden(sK5(sK4(k1_xboole_0,sK3),k1_xboole_0,X1),k1_xboole_0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f465,f332])).
% 1.35/0.56  fof(f332,plain,(
% 1.35/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.35/0.56    inference(forward_demodulation,[],[f329,f94])).
% 1.35/0.56  fof(f94,plain,(
% 1.35/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.35/0.56    inference(equality_resolution,[],[f77])).
% 1.35/0.56  fof(f77,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.35/0.56    inference(cnf_transformation,[],[f48])).
% 1.35/0.56  fof(f329,plain,(
% 1.35/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.35/0.56    inference(backward_demodulation,[],[f57,f325])).
% 1.35/0.56  fof(f325,plain,(
% 1.35/0.56    k1_xboole_0 = sK2),
% 1.35/0.56    inference(subsumption_resolution,[],[f324,f103])).
% 1.35/0.56  fof(f103,plain,(
% 1.35/0.56    ~v1_funct_2(sK3,sK1,sK2)),
% 1.35/0.56    inference(subsumption_resolution,[],[f102,f56])).
% 1.35/0.56  fof(f102,plain,(
% 1.35/0.56    ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f59,f57])).
% 1.35/0.56  fof(f59,plain,(
% 1.35/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 1.35/0.56    inference(cnf_transformation,[],[f44])).
% 1.35/0.56  fof(f324,plain,(
% 1.35/0.56    k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,sK2)),
% 1.35/0.56    inference(subsumption_resolution,[],[f322,f58])).
% 1.35/0.56  fof(f58,plain,(
% 1.35/0.56    sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.35/0.56    inference(cnf_transformation,[],[f44])).
% 1.35/0.56  fof(f322,plain,(
% 1.35/0.56    sK1 != k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,sK2)),
% 1.35/0.56    inference(resolution,[],[f82,f144])).
% 1.35/0.56  fof(f144,plain,(
% 1.35/0.56    sP0(sK1,sK3,sK2)),
% 1.35/0.56    inference(resolution,[],[f84,f57])).
% 1.35/0.56  fof(f82,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f50])).
% 1.35/0.56  fof(f465,plain,(
% 1.35/0.56    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 | r2_hidden(sK5(sK4(k1_xboole_0,sK3),k1_xboole_0,X1),k1_xboole_0)) )),
% 1.35/0.56    inference(superposition,[],[f460,f95])).
% 1.35/0.56  fof(f460,plain,(
% 1.35/0.56    ( ! [X8,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k1_xboole_0 = sK3 | r2_hidden(sK5(sK4(k1_xboole_0,sK3),X7,X8),X7)) )),
% 1.35/0.56    inference(resolution,[],[f289,f332])).
% 1.35/0.56  fof(f289,plain,(
% 1.35/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X1 | r2_hidden(sK5(sK4(X0,X1),X2,X3),X2)) )),
% 1.35/0.56    inference(resolution,[],[f92,f71])).
% 1.35/0.56  fof(f71,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f46])).
% 1.35/0.56  fof(f46,plain,(
% 1.35/0.56    ! [X0,X1] : ((r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f45])).
% 1.35/0.56  fof(f45,plain,(
% 1.35/0.56    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f26,plain,(
% 1.35/0.56    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.56    inference(flattening,[],[f25])).
% 1.35/0.56  fof(f25,plain,(
% 1.35/0.56    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f5])).
% 1.35/0.56  fof(f5,axiom,(
% 1.35/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.35/0.56  fof(f92,plain,(
% 1.35/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X3) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f55])).
% 1.35/0.56  fof(f55,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f54])).
% 1.35/0.56  fof(f54,plain,(
% 1.35/0.56    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f40,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.35/0.56    inference(flattening,[],[f39])).
% 1.35/0.56  fof(f39,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.35/0.56    inference(ennf_transformation,[],[f14])).
% 1.35/0.56  fof(f14,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 1.35/0.56  fof(f208,plain,(
% 1.35/0.56    sK1 = k1_relat_1(sK3)),
% 1.35/0.56    inference(forward_demodulation,[],[f204,f58])).
% 1.35/0.56  fof(f204,plain,(
% 1.35/0.56    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 1.35/0.56    inference(resolution,[],[f79,f57])).
% 1.35/0.56  fof(f494,plain,(
% 1.35/0.56    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 1.35/0.56    inference(backward_demodulation,[],[f328,f471])).
% 1.35/0.56  fof(f328,plain,(
% 1.35/0.56    ~v1_funct_2(sK3,sK1,k1_xboole_0)),
% 1.35/0.56    inference(backward_demodulation,[],[f103,f325])).
% 1.35/0.56  % SZS output end Proof for theBenchmark
% 1.35/0.56  % (12058)------------------------------
% 1.35/0.56  % (12058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (12058)Termination reason: Refutation
% 1.35/0.56  
% 1.35/0.56  % (12058)Memory used [KB]: 6524
% 1.35/0.56  % (12058)Time elapsed: 0.100 s
% 1.35/0.56  % (12058)------------------------------
% 1.35/0.56  % (12058)------------------------------
% 1.35/0.56  % (12061)Refutation not found, incomplete strategy% (12061)------------------------------
% 1.35/0.56  % (12061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (12061)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (12061)Memory used [KB]: 10618
% 1.35/0.56  % (12061)Time elapsed: 0.158 s
% 1.35/0.56  % (12061)------------------------------
% 1.35/0.56  % (12061)------------------------------
% 1.35/0.56  % (12048)Success in time 0.199 s
%------------------------------------------------------------------------------
