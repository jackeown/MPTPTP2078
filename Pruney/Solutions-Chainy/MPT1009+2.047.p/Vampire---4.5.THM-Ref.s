%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:32 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 613 expanded)
%              Number of leaves         :   19 ( 172 expanded)
%              Depth                    :   18
%              Number of atoms          :  326 (1783 expanded)
%              Number of equality atoms :  146 ( 663 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f115])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f114,f108])).

fof(f108,plain,(
    k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)) = k2_relat_1(sK5) ),
    inference(superposition,[],[f104,f106])).

fof(f106,plain,(
    sK5 = k7_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f105,f99])).

fof(f99,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f60,f83])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f49,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK5,k1_tarski(sK2),sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK5,k1_tarski(sK2),sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

% (5876)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f105,plain,
    ( sK5 = k7_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f58,f102])).

fof(f102,plain,(
    v4_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f62,f83])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f104,plain,(
    ! [X0] : k9_relat_1(sK5,X0) = k2_relat_1(k7_relat_1(sK5,X0)) ),
    inference(resolution,[],[f56,f99])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f114,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(subsumption_resolution,[],[f112,f99])).

fof(f112,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)))
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f107,f106])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK5,X0),X1),k9_relat_1(sK5,X0))
      | ~ v1_relat_1(k7_relat_1(sK5,X0)) ) ),
    inference(superposition,[],[f55,f104])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f194,plain,(
    ~ r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f180,f193])).

fof(f193,plain,(
    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5) ),
    inference(forward_demodulation,[],[f192,f123])).

fof(f123,plain,(
    k2_relat_1(sK5) = k11_relat_1(sK5,sK2) ),
    inference(superposition,[],[f122,f108])).

fof(f122,plain,(
    ! [X0] : k11_relat_1(sK5,X0) = k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f85,f99])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f192,plain,(
    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f191,f99])).

fof(f191,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f189,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f189,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f86,f146])).

fof(f146,plain,(
    r2_hidden(sK2,k1_relat_1(sK5)) ),
    inference(superposition,[],[f101,f136])).

fof(f136,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK5) ),
    inference(forward_demodulation,[],[f135,f120])).

fof(f120,plain,(
    k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f61,f83])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f135,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f134,plain,
    ( k1_xboole_0 = sK3
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5) ),
    inference(subsumption_resolution,[],[f133,f84])).

fof(f84,plain,(
    v1_funct_2(sK5,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f48,f81])).

fof(f48,plain,(
    v1_funct_2(sK5,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f133,plain,
    ( ~ v1_funct_2(sK5,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | k1_xboole_0 = sK3
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5) ),
    inference(resolution,[],[f64,f111])).

fof(f111,plain,(
    sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK5,sK3) ),
    inference(resolution,[],[f68,f83])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f101,plain,(
    ! [X2,X3] : r2_hidden(X2,k2_enumset1(X3,X3,X3,X2)) ),
    inference(resolution,[],[f96,f94])).

fof(f94,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f96,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f180,plain,(
    ~ r1_tarski(k9_relat_1(sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(backward_demodulation,[],[f176,f144])).

fof(f144,plain,(
    ! [X0] : k9_relat_1(sK5,X0) = k7_relset_1(k1_relat_1(sK5),sK3,sK5,X0) ),
    inference(backward_demodulation,[],[f132,f136])).

fof(f132,plain,(
    ! [X0] : k9_relat_1(sK5,X0) = k7_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5,X0) ),
    inference(resolution,[],[f79,f83])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f176,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1(sK5),sK3,sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(forward_demodulation,[],[f82,f136])).

fof(f82,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(definition_unfolding,[],[f51,f81,f81])).

fof(f51,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (5851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (5882)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.53  % (5874)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (5865)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (5873)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.53  % (5855)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.53  % (5858)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.53  % (5865)Refutation not found, incomplete strategy% (5865)------------------------------
% 1.27/0.53  % (5865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (5865)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (5865)Memory used [KB]: 1791
% 1.27/0.53  % (5865)Time elapsed: 0.056 s
% 1.27/0.53  % (5865)------------------------------
% 1.27/0.53  % (5865)------------------------------
% 1.27/0.53  % (5864)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.54  % (5857)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.54  % (5857)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % (5870)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (5882)Refutation not found, incomplete strategy% (5882)------------------------------
% 1.36/0.54  % (5882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (5882)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (5882)Memory used [KB]: 1663
% 1.36/0.54  % (5882)Time elapsed: 0.134 s
% 1.36/0.54  % (5882)------------------------------
% 1.36/0.54  % (5882)------------------------------
% 1.36/0.55  % (5854)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f202,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f194,f115])).
% 1.36/0.55  fof(f115,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f114,f108])).
% 1.36/0.55  fof(f108,plain,(
% 1.36/0.55    k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)) = k2_relat_1(sK5)),
% 1.36/0.55    inference(superposition,[],[f104,f106])).
% 1.36/0.55  fof(f106,plain,(
% 1.36/0.55    sK5 = k7_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.36/0.55    inference(subsumption_resolution,[],[f105,f99])).
% 1.36/0.55  fof(f99,plain,(
% 1.36/0.55    v1_relat_1(sK5)),
% 1.36/0.55    inference(resolution,[],[f60,f83])).
% 1.36/0.55  fof(f83,plain,(
% 1.36/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 1.36/0.55    inference(definition_unfolding,[],[f49,f81])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f52,f80])).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f54,f59])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.36/0.55    inference(flattening,[],[f17])).
% 1.36/0.55  fof(f17,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.36/0.55    inference(ennf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.55    inference(negated_conjecture,[],[f15])).
% 1.36/0.55  fof(f15,conjecture,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.36/0.55  fof(f60,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f26])).
% 1.36/0.55  % (5876)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.55  fof(f105,plain,(
% 1.36/0.55    sK5 = k7_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)) | ~v1_relat_1(sK5)),
% 1.36/0.55    inference(resolution,[],[f58,f102])).
% 1.36/0.55  fof(f102,plain,(
% 1.36/0.55    v4_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.36/0.55    inference(resolution,[],[f62,f83])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(flattening,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.36/0.55  fof(f104,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK5,X0) = k2_relat_1(k7_relat_1(sK5,X0))) )),
% 1.36/0.55    inference(resolution,[],[f56,f99])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.36/0.55  fof(f114,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2)))) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f112,f99])).
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,k2_enumset1(sK2,sK2,sK2,sK2))) | ~v1_relat_1(sK5)) )),
% 1.36/0.55    inference(superposition,[],[f107,f106])).
% 1.36/0.55  fof(f107,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK5,X0),X1),k9_relat_1(sK5,X0)) | ~v1_relat_1(k7_relat_1(sK5,X0))) )),
% 1.36/0.55    inference(superposition,[],[f55,f104])).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.36/0.55  fof(f194,plain,(
% 1.36/0.55    ~r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5))),
% 1.36/0.55    inference(backward_demodulation,[],[f180,f193])).
% 1.36/0.55  fof(f193,plain,(
% 1.36/0.55    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)),
% 1.36/0.55    inference(forward_demodulation,[],[f192,f123])).
% 1.36/0.55  fof(f123,plain,(
% 1.36/0.55    k2_relat_1(sK5) = k11_relat_1(sK5,sK2)),
% 1.36/0.55    inference(superposition,[],[f122,f108])).
% 1.36/0.55  fof(f122,plain,(
% 1.36/0.55    ( ! [X0] : (k11_relat_1(sK5,X0) = k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) )),
% 1.36/0.55    inference(resolution,[],[f85,f99])).
% 1.36/0.55  fof(f85,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f53,f81])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f19])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.36/0.55  fof(f192,plain,(
% 1.36/0.55    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)),
% 1.36/0.55    inference(subsumption_resolution,[],[f191,f99])).
% 1.36/0.55  fof(f191,plain,(
% 1.36/0.55    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) | ~v1_relat_1(sK5)),
% 1.36/0.55    inference(subsumption_resolution,[],[f189,f47])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    v1_funct_1(sK5)),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f189,plain,(
% 1.36/0.55    k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 1.36/0.55    inference(resolution,[],[f86,f146])).
% 1.36/0.55  fof(f146,plain,(
% 1.36/0.55    r2_hidden(sK2,k1_relat_1(sK5))),
% 1.36/0.55    inference(superposition,[],[f101,f136])).
% 1.36/0.55  fof(f136,plain,(
% 1.36/0.55    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK5)),
% 1.36/0.55    inference(forward_demodulation,[],[f135,f120])).
% 1.36/0.55  fof(f120,plain,(
% 1.36/0.55    k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5) = k1_relat_1(sK5)),
% 1.36/0.55    inference(resolution,[],[f61,f83])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.55  fof(f135,plain,(
% 1.36/0.55    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5)),
% 1.36/0.55    inference(subsumption_resolution,[],[f134,f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    k1_xboole_0 != sK3),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f134,plain,(
% 1.36/0.55    k1_xboole_0 = sK3 | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5)),
% 1.36/0.55    inference(subsumption_resolution,[],[f133,f84])).
% 1.36/0.55  fof(f84,plain,(
% 1.36/0.55    v1_funct_2(sK5,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 1.36/0.55    inference(definition_unfolding,[],[f48,f81])).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    v1_funct_2(sK5,k1_tarski(sK2),sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f133,plain,(
% 1.36/0.55    ~v1_funct_2(sK5,k2_enumset1(sK2,sK2,sK2,sK2),sK3) | k1_xboole_0 = sK3 | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5)),
% 1.36/0.55    inference(resolution,[],[f64,f111])).
% 1.36/0.55  fof(f111,plain,(
% 1.36/0.55    sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK5,sK3)),
% 1.36/0.55    inference(resolution,[],[f68,f83])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(nnf_transformation,[],[f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(definition_folding,[],[f30,f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.36/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(flattening,[],[f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.36/0.55    inference(rectify,[],[f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f32])).
% 1.36/0.55  fof(f101,plain,(
% 1.36/0.55    ( ! [X2,X3] : (r2_hidden(X2,k2_enumset1(X3,X3,X3,X2))) )),
% 1.36/0.55    inference(resolution,[],[f96,f94])).
% 1.36/0.55  fof(f94,plain,(
% 1.36/0.55    ( ! [X4,X2,X1] : (~sP1(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.36/0.55    inference(equality_resolution,[],[f73])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP1(X0,X1,X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f45])).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.36/0.55    inference(rectify,[],[f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.36/0.55    inference(flattening,[],[f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.36/0.55    inference(nnf_transformation,[],[f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.36/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.36/0.55  fof(f96,plain,(
% 1.36/0.55    ( ! [X0,X1] : (sP1(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.36/0.55    inference(equality_resolution,[],[f88])).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.36/0.55    inference(definition_unfolding,[],[f77,f80])).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.36/0.55    inference(cnf_transformation,[],[f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.36/0.55    inference(nnf_transformation,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.36/0.55    inference(definition_folding,[],[f1,f34])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.36/0.55  fof(f86,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f57,f81])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(flattening,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.36/0.55  fof(f180,plain,(
% 1.36/0.55    ~r1_tarski(k9_relat_1(sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 1.36/0.55    inference(backward_demodulation,[],[f176,f144])).
% 1.36/0.55  fof(f144,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK5,X0) = k7_relset_1(k1_relat_1(sK5),sK3,sK5,X0)) )),
% 1.36/0.55    inference(backward_demodulation,[],[f132,f136])).
% 1.36/0.55  fof(f132,plain,(
% 1.36/0.55    ( ! [X0] : (k9_relat_1(sK5,X0) = k7_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5,X0)) )),
% 1.36/0.55    inference(resolution,[],[f79,f83])).
% 1.36/0.55  fof(f79,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.36/0.55  fof(f176,plain,(
% 1.36/0.55    ~r1_tarski(k7_relset_1(k1_relat_1(sK5),sK3,sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 1.36/0.55    inference(forward_demodulation,[],[f82,f136])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ~r1_tarski(k7_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK5,sK4),k2_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 1.36/0.55    inference(definition_unfolding,[],[f51,f81,f81])).
% 1.36/0.55  fof(f51,plain,(
% 1.36/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (5857)------------------------------
% 1.36/0.55  % (5857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (5857)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (5857)Memory used [KB]: 10874
% 1.36/0.55  % (5857)Time elapsed: 0.110 s
% 1.36/0.55  % (5857)------------------------------
% 1.36/0.55  % (5857)------------------------------
% 1.36/0.55  % (5852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.55  % (5850)Success in time 0.181 s
%------------------------------------------------------------------------------
