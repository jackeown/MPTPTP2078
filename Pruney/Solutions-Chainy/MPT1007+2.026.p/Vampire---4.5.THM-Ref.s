%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 414 expanded)
%              Number of leaves         :   19 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  249 ( 915 expanded)
%              Number of equality atoms :   97 ( 321 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2353)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f224,plain,(
    $false ),
    inference(subsumption_resolution,[],[f221,f217])).

fof(f217,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X0) != k1_relset_1(k2_enumset1(X0,X0,X0,X0),X1,k1_xboole_0) ),
    inference(resolution,[],[f214,f81])).

fof(f81,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f214,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relset_1(X0,X1,k1_xboole_0) != X0 ) ),
    inference(resolution,[],[f213,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | k1_relset_1(X0,X1,k1_xboole_0) != X0 ) ),
    inference(subsumption_resolution,[],[f212,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) != X0
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k4_tarski(X2,sK5(k1_xboole_0,X2)),k1_xboole_0) ) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f221,plain,(
    ! [X4] : k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),X4,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,(
    ! [X4] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),X4,k1_xboole_0) ) ),
    inference(superposition,[],[f216,f210])).

fof(f210,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f207,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f207,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f204,f144])).

fof(f144,plain,(
    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f80,f140])).

fof(f140,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f113,f133])).

fof(f133,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f119,f132])).

fof(f132,plain,(
    k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f131,f92])).

fof(f92,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f45,f78])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f131,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f128,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f127,f47])).

fof(f47,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f126,f96])).

fof(f96,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f66,f79])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X0)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X1),X0) ) ),
    inference(subsumption_resolution,[],[f125,f92])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X1),X0) ) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f119,plain,(
    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    inference(superposition,[],[f114,f106])).

fof(f106,plain,(
    k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f97,f105])).

fof(f105,plain,(
    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f101,f94])).

fof(f94,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f65,f79])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f61,f92])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f57,f92])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f114,plain,(
    ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f82,f92])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f113,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f112,f106])).

fof(f112,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f111,f92])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 != k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f99,f105])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | k1_xboole_0 != k9_relat_1(sK2,X0)
      | k1_xboole_0 = k7_relat_1(sK2,X0) ) ),
    inference(superposition,[],[f53,f97])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f80,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f44,f78])).

fof(f44,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X1,X0)
      | k1_relset_1(X1,X0,k1_xboole_0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f216,plain,(
    ! [X6,X7,X5] :
      ( k1_relset_1(X5,X6,k1_xboole_0) != X5
      | k1_relset_1(X5,X7,k1_xboole_0) = X5 ) ),
    inference(resolution,[],[f213,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_relset_1(X0,X1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f73,f50])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK4(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (2356)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (2366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (2358)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2370)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (2350)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (2366)Refutation not found, incomplete strategy% (2366)------------------------------
% 0.21/0.51  % (2366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2366)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2366)Memory used [KB]: 10746
% 0.21/0.51  % (2366)Time elapsed: 0.055 s
% 0.21/0.51  % (2366)------------------------------
% 0.21/0.51  % (2366)------------------------------
% 0.21/0.51  % (2362)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (2344)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (2355)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (2350)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (2349)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (2353)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f221,f217])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) != k1_relset_1(k2_enumset1(X0,X0,X0,X0),X1,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f214,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f48,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f51,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f56,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relset_1(X0,X1,k1_xboole_0) != X0) )),
% 0.21/0.52    inference(resolution,[],[f213,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | k1_relset_1(X0,X1,k1_xboole_0) != X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f212,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f62,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) != X0 | ~r2_hidden(X2,X0) | r2_hidden(k4_tarski(X2,sK5(k1_xboole_0,X2)),k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f75,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    ( ! [X4] : (k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),X4,k1_xboole_0)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    ( ! [X4] : (k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),X4,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f216,f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f20])).
% 0.21/0.52  fof(f20,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.52    inference(resolution,[],[f204,f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f80,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k1_xboole_0 = sK2),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f113,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f119,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f131,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f64,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.52    inference(definition_unfolding,[],[f45,f78])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    k1_xboole_0 = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f128,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f127,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.21/0.52    inference(resolution,[],[f126,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    v5_relat_1(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f66,f79])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(sK2,X0) | ~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X1),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f92])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2) | ~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X1),X0)) )),
% 0.21/0.52    inference(resolution,[],[f60,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 0.21/0.52    inference(superposition,[],[f114,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK2)),
% 0.21/0.52    inference(superposition,[],[f97,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f101,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f65,f79])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f61,f92])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f57,f92])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.52    inference(resolution,[],[f82,f92])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f54,f78])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f112,f106])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    k1_xboole_0 != k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f92])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | k1_xboole_0 != k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f99,f105])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK2,X0)) | k1_xboole_0 != k9_relat_1(sK2,X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) )),
% 0.21/0.52    inference(superposition,[],[f53,f97])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f44,f78])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X1,X0) | k1_relset_1(X1,X0,k1_xboole_0) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f72,f50])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (k1_relset_1(X5,X6,k1_xboole_0) != X5 | k1_relset_1(X5,X7,k1_xboole_0) = X5) )),
% 0.21/0.52    inference(resolution,[],[f213,f194])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_relset_1(X0,X1,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(resolution,[],[f73,f50])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK4(X1,X2),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2350)------------------------------
% 0.21/0.52  % (2350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2350)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2350)Memory used [KB]: 6268
% 0.21/0.52  % (2350)Time elapsed: 0.065 s
% 0.21/0.52  % (2350)------------------------------
% 0.21/0.52  % (2350)------------------------------
% 0.21/0.52  % (2343)Success in time 0.166 s
%------------------------------------------------------------------------------
