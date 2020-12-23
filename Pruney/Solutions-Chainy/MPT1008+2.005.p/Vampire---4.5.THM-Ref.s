%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:08 EST 2020

% Result     : Theorem 3.39s
% Output     : Refutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  309 (2728 expanded)
%              Number of leaves         :   46 ( 782 expanded)
%              Depth                    :   21
%              Number of atoms          :  958 (6689 expanded)
%              Number of equality atoms :  325 (2874 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f565,f1017,f1312,f1480,f1925,f1954,f2177,f2204,f3466,f3573,f3872,f4149,f4175,f4474,f4600])).

fof(f4600,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_43 ),
    inference(avatar_contradiction_clause,[],[f4599])).

fof(f4599,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f4598,f3676])).

fof(f3676,plain,
    ( o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f3675,f185])).

fof(f185,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f87,f182])).

fof(f182,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f92,f85])).

fof(f85,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f87,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f3675,plain,
    ( k2_relat_1(o_0_0_xboole_0) != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f1512,f762])).

fof(f762,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_4 ),
    inference(resolution,[],[f282,f183])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f92,f182])).

fof(f282,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1512,plain,
    ( k2_relat_1(sK3) != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f620,f1491])).

fof(f1491,plain,
    ( o_0_0_xboole_0 = k1_funct_1(sK3,sK1)
    | ~ spl6_43 ),
    inference(resolution,[],[f1449,f183])).

fof(f1449,plain,
    ( v1_xboole_0(k1_funct_1(sK3,sK1))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1447,plain,
    ( spl6_43
  <=> v1_xboole_0(k1_funct_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f620,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f146,f443])).

fof(f443,plain,(
    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f121,f147])).

fof(f147,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f82,f145])).

fof(f145,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f91,f144])).

fof(f144,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f99,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f63])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f146,plain,(
    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) ),
    inference(definition_unfolding,[],[f84,f145,f145])).

fof(f84,plain,(
    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f4598,plain,
    ( o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f2563,f4104])).

fof(f4104,plain,
    ( ! [X0] : o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f4072,f85])).

fof(f4072,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0) )
    | ~ spl6_4 ),
    inference(superposition,[],[f149,f3576])).

fof(f3576,plain,
    ( ! [X10] :
        ( o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10))
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X10) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f3575,f762])).

fof(f3575,plain,
    ( ! [X10] :
        ( o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10))
        | o_0_0_xboole_0 = k1_funct_1(sK3,X10) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f3558,f498])).

fof(f498,plain,(
    ! [X0] : o_0_0_xboole_0 = k11_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f493,f389])).

fof(f389,plain,(
    ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f388,f185])).

fof(f388,plain,(
    ! [X0] : k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f295,f312])).

fof(f312,plain,(
    ! [X2] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f307,f202])).

fof(f202,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f120,f184])).

fof(f184,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f90,f182])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f307,plain,(
    ! [X2] :
      ( o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X2)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(resolution,[],[f106,f230])).

fof(f230,plain,(
    ! [X0] : v4_relat_1(o_0_0_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f229,f202])).

fof(f229,plain,(
    ! [X0] :
      ( v4_relat_1(o_0_0_xboole_0,X0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(subsumption_resolution,[],[f227,f187])).

fof(f187,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(backward_demodulation,[],[f89,f182])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f227,plain,(
    ! [X0] :
      ( ~ r1_tarski(o_0_0_xboole_0,X0)
      | v4_relat_1(o_0_0_xboole_0,X0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f103,f186])).

fof(f186,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f86,f182])).

fof(f86,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f295,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(resolution,[],[f101,f202])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f493,plain,(
    ! [X0] : k11_relat_1(o_0_0_xboole_0,X0) = k9_relat_1(o_0_0_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f150,f202])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f93,f145])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f3558,plain,
    ( ! [X10] :
        ( k11_relat_1(o_0_0_xboole_0,X10) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10))
        | o_0_0_xboole_0 = k1_funct_1(sK3,X10) )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f1740,f762])).

fof(f1740,plain,(
    ! [X10] :
      ( k11_relat_1(sK3,X10) = k2_enumset1(k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10))
      | o_0_0_xboole_0 = k1_funct_1(sK3,X10) ) ),
    inference(subsumption_resolution,[],[f1730,f203])).

fof(f203,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f120,f147])).

fof(f1730,plain,(
    ! [X10] :
      ( k11_relat_1(sK3,X10) = k2_enumset1(k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10))
      | ~ v1_relat_1(sK3)
      | o_0_0_xboole_0 = k1_funct_1(sK3,X10) ) ),
    inference(resolution,[],[f675,f80])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f675,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k11_relat_1(X0,X1) = k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1))
      | ~ v1_relat_1(X0)
      | o_0_0_xboole_0 = k1_funct_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f671])).

fof(f671,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | o_0_0_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f151,f501])).

fof(f501,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | o_0_0_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f164,f182])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f104,f145])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f149,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f88,f145])).

fof(f88,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f2563,plain,
    ( o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)))
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(resolution,[],[f634,f678])).

fof(f678,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f677,f498])).

fof(f677,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0)) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f676,f202])).

fof(f676,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0))
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f674,f266])).

fof(f266,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl6_2
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f674,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,o_0_0_xboole_0)
      | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0))
      | ~ v1_funct_1(o_0_0_xboole_0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f151,f186])).

fof(f634,plain,
    ( r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl6_17
  <=> r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f4474,plain,
    ( ~ spl6_4
    | spl6_17
    | ~ spl6_22
    | ~ spl6_43
    | ~ spl6_169 ),
    inference(avatar_contradiction_clause,[],[f4473])).

fof(f4473,plain,
    ( $false
    | ~ spl6_4
    | spl6_17
    | ~ spl6_22
    | ~ spl6_43
    | ~ spl6_169 ),
    inference(subsumption_resolution,[],[f4466,f3674])).

fof(f3674,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f3673,f185])).

fof(f3673,plain,
    ( r2_hidden(o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f1513,f762])).

fof(f1513,plain,
    ( r2_hidden(o_0_0_xboole_0,k2_relat_1(sK3))
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f1383,f1491])).

fof(f1383,plain,(
    r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f728,f207])).

fof(f207,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f171,f170])).

fof(f170,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f171,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f132,f144])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f728,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f727,f80])).

fof(f727,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
      | ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f726,f148])).

fof(f148,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f81,f145])).

fof(f81,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f726,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
      | ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f725,f147])).

fof(f725,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
      | ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
      | ~ v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f704,f188])).

fof(f188,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f83,f182])).

fof(f83,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f64])).

fof(f704,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
      | o_0_0_xboole_0 = sK2
      | ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
      | ~ v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f699,f443])).

fof(f699,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(forward_demodulation,[],[f134,f182])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f4466,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | spl6_17
    | ~ spl6_22
    | ~ spl6_169 ),
    inference(backward_demodulation,[],[f4344,f4351])).

fof(f4351,plain,
    ( o_0_0_xboole_0 = k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_22
    | ~ spl6_169 ),
    inference(resolution,[],[f4345,f183])).

fof(f4345,plain,
    ( v1_xboole_0(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl6_22
    | ~ spl6_169 ),
    inference(forward_demodulation,[],[f4174,f1012])).

fof(f1012,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1010,plain,
    ( spl6_22
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f4174,plain,
    ( v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0))
    | ~ spl6_169 ),
    inference(avatar_component_clause,[],[f4172])).

fof(f4172,plain,
    ( spl6_169
  <=> v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).

fof(f4344,plain,
    ( ~ r2_hidden(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_4
    | spl6_17 ),
    inference(forward_demodulation,[],[f4343,f185])).

fof(f4343,plain,
    ( ~ r2_hidden(k4_tarski(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_4
    | spl6_17 ),
    inference(forward_demodulation,[],[f633,f762])).

fof(f633,plain,
    ( ~ r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f632])).

fof(f4175,plain,
    ( ~ spl6_139
    | spl6_169
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f4038,f280,f264,f4172,f3666])).

fof(f3666,plain,
    ( spl6_139
  <=> r2_hidden(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f4038,plain,
    ( v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0))
    | ~ r2_hidden(sK1,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f1822,f4029])).

fof(f4029,plain,
    ( o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,sK1)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f3490,f762])).

fof(f3490,plain,(
    o_0_0_xboole_0 = k1_funct_1(sK3,sK1) ),
    inference(global_subsumption,[],[f499,f3413])).

fof(f3413,plain,
    ( k2_relat_1(sK3) != k11_relat_1(sK3,sK1)
    | o_0_0_xboole_0 = k1_funct_1(sK3,sK1) ),
    inference(superposition,[],[f620,f1740])).

fof(f499,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[],[f496,f365])).

fof(f365,plain,(
    k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[],[f298,f313])).

fof(f313,plain,(
    sK3 = k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f308,f203])).

fof(f308,plain,
    ( sK3 = k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f238])).

fof(f238,plain,(
    v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f123,f147])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f298,plain,(
    ! [X5] : k2_relat_1(k7_relat_1(sK3,X5)) = k9_relat_1(sK3,X5) ),
    inference(resolution,[],[f101,f203])).

fof(f496,plain,(
    ! [X6] : k11_relat_1(sK3,X6) = k9_relat_1(sK3,k2_enumset1(X6,X6,X6,X6)) ),
    inference(resolution,[],[f150,f203])).

fof(f1822,plain,
    ( ! [X53] :
        ( v1_xboole_0(k4_tarski(X53,k1_funct_1(o_0_0_xboole_0,X53)))
        | ~ r2_hidden(X53,o_0_0_xboole_0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f574,f284])).

fof(f284,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f273,f85])).

fof(f273,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f100,f189])).

fof(f189,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f167,f182])).

fof(f167,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f574,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4)
        | ~ r2_hidden(X3,o_0_0_xboole_0) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f573,f186])).

fof(f573,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(o_0_0_xboole_0))
        | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f572,f202])).

fof(f572,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(o_0_0_xboole_0))
        | ~ v1_relat_1(o_0_0_xboole_0)
        | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f569,f266])).

fof(f569,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(o_0_0_xboole_0))
      | ~ v1_funct_1(o_0_0_xboole_0)
      | ~ v1_relat_1(o_0_0_xboole_0)
      | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4) ) ),
    inference(resolution,[],[f166,f341])).

fof(f341,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,o_0_0_xboole_0)
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f125,f184])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f166,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f4149,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | spl6_23
    | ~ spl6_43 ),
    inference(avatar_contradiction_clause,[],[f4146])).

fof(f4146,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | spl6_23
    | ~ spl6_43 ),
    inference(resolution,[],[f4131,f3674])).

fof(f4131,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_23 ),
    inference(subsumption_resolution,[],[f4121,f1016])).

fof(f1016,plain,
    ( o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1014,plain,
    ( spl6_23
  <=> o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f4121,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ r2_hidden(X0,o_0_0_xboole_0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f678,f4104])).

fof(f3872,plain,
    ( ~ spl6_4
    | ~ spl6_22
    | ~ spl6_43
    | spl6_139 ),
    inference(avatar_contradiction_clause,[],[f3871])).

fof(f3871,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_22
    | ~ spl6_43
    | spl6_139 ),
    inference(subsumption_resolution,[],[f3870,f3674])).

fof(f3870,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_22
    | spl6_139 ),
    inference(forward_demodulation,[],[f3668,f1012])).

fof(f3668,plain,
    ( ~ r2_hidden(sK1,o_0_0_xboole_0)
    | spl6_139 ),
    inference(avatar_component_clause,[],[f3666])).

fof(f3573,plain,
    ( ~ spl6_4
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f3572])).

fof(f3572,plain,
    ( $false
    | ~ spl6_4
    | spl6_47 ),
    inference(subsumption_resolution,[],[f3571,f187])).

fof(f3571,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | spl6_47 ),
    inference(forward_demodulation,[],[f3556,f185])).

fof(f3556,plain,
    ( ~ r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | spl6_47 ),
    inference(backward_demodulation,[],[f1465,f762])).

fof(f1465,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f1463])).

fof(f1463,plain,
    ( spl6_47
  <=> r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f3466,plain,
    ( spl6_43
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f3465])).

fof(f3465,plain,
    ( $false
    | spl6_43
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f3452,f85])).

fof(f3452,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl6_43
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f1448,f3447])).

fof(f3447,plain,
    ( o_0_0_xboole_0 = k1_funct_1(sK3,sK1)
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f3413,f3076])).

fof(f3076,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK1)
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f3047,f2116])).

fof(f2116,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f365,f1924])).

fof(f1924,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f1922])).

fof(f1922,plain,
    ( spl6_66
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f3047,plain,
    ( k11_relat_1(sK3,sK1) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl6_66 ),
    inference(superposition,[],[f496,f1924])).

fof(f1448,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK3,sK1))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f2204,plain,
    ( spl6_4
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f2203])).

fof(f2203,plain,
    ( $false
    | spl6_4
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f2197,f281])).

fof(f281,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f280])).

fof(f2197,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_36 ),
    inference(resolution,[],[f1311,f284])).

fof(f1311,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f1309])).

fof(f1309,plain,
    ( spl6_36
  <=> m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f2177,plain,
    ( ~ spl6_43
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f2176])).

fof(f2176,plain,
    ( $false
    | ~ spl6_43
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f2175,f1512])).

fof(f2175,plain,
    ( k2_relat_1(sK3) = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_43
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f2174,f1491])).

fof(f2174,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f2173,f499])).

fof(f2173,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1)
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f2172,f203])).

fof(f2172,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f2162,f80])).

fof(f2162,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_66 ),
    inference(resolution,[],[f2132,f151])).

fof(f2132,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3))
    | ~ spl6_66 ),
    inference(superposition,[],[f207,f1924])).

fof(f1954,plain,
    ( spl6_35
    | ~ spl6_65 ),
    inference(avatar_contradiction_clause,[],[f1953])).

fof(f1953,plain,
    ( $false
    | spl6_35
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1931,f187])).

fof(f1931,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | spl6_35
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f1307,f1920])).

fof(f1920,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f1918])).

fof(f1918,plain,
    ( spl6_65
  <=> o_0_0_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1307,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1305,plain,
    ( spl6_35
  <=> r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1925,plain,
    ( spl6_65
    | spl6_66 ),
    inference(avatar_split_clause,[],[f1916,f1922,f1918])).

fof(f1916,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | o_0_0_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1915,f203])).

fof(f1915,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | o_0_0_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f1908])).

fof(f1908,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | o_0_0_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f836,f238])).

fof(f836,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ v4_relat_1(X31,k2_enumset1(X28,X28,X29,X30))
      | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X30)
      | k1_relat_1(X31) = k2_enumset1(X29,X29,X29,X30)
      | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X29)
      | k1_relat_1(X31) = k2_enumset1(X30,X30,X30,X30)
      | k1_relat_1(X31) = k2_enumset1(X29,X29,X29,X29)
      | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X28)
      | o_0_0_xboole_0 = k1_relat_1(X31)
      | k2_enumset1(X28,X28,X29,X30) = k1_relat_1(X31)
      | ~ v1_relat_1(X31) ) ),
    inference(resolution,[],[f759,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f759,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | o_0_0_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f163,f182])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f135,f118,f144,f144,f144,f145,f145,f145,f118])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f1480,plain,
    ( spl6_43
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f1435,f1463,f1447])).

fof(f1435,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_funct_1(sK3,sK1)) ),
    inference(resolution,[],[f1401,f284])).

fof(f1401,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK3,sK1),X0)
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f1383,f340])).

fof(f340,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f125,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1312,plain,
    ( ~ spl6_35
    | spl6_36 ),
    inference(avatar_split_clause,[],[f1303,f1309,f1305])).

fof(f1303,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f1299,f203])).

fof(f1299,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f471,f603])).

fof(f603,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X3),X2)
      | m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
      | ~ r1_tarski(k1_relat_1(X3),o_0_0_xboole_0)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f119,f190])).

fof(f190,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(forward_demodulation,[],[f168,f182])).

fof(f168,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f471,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(resolution,[],[f468,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f468,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f462,f147])).

fof(f462,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(superposition,[],[f122,f443])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f1017,plain,
    ( spl6_22
    | ~ spl6_23
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f1006,f280,f264,f1014,f1010])).

fof(f1006,plain,
    ( o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f798,f623])).

fof(f623,plain,
    ( ! [X5] :
        ( o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X5)
        | o_0_0_xboole_0 = X5 )
    | ~ spl6_2 ),
    inference(resolution,[],[f547,f183])).

fof(f547,plain,
    ( ! [X20] :
        ( v1_xboole_0(X20)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X20) )
    | ~ spl6_2 ),
    inference(resolution,[],[f534,f284])).

fof(f534,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f533,f341])).

fof(f533,plain,
    ( ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f532,f202])).

fof(f532,plain,
    ( ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f531,f266])).

fof(f531,plain,(
    ! [X0] :
      ( r2_hidden(X0,o_0_0_xboole_0)
      | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)
      | ~ v1_funct_1(o_0_0_xboole_0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f501,f186])).

fof(f798,plain,
    ( o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f783,f185])).

fof(f783,plain,
    ( k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f620,f762])).

fof(f565,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f329,f265])).

fof(f265,plain,
    ( ~ v1_funct_1(o_0_0_xboole_0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f264])).

fof(f329,plain,(
    v1_funct_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f116,f304])).

fof(f304,plain,(
    ! [X0] : o_0_0_xboole_0 = sK4(X0,o_0_0_xboole_0) ),
    inference(resolution,[],[f302,f183])).

fof(f302,plain,(
    ! [X1] : v1_xboole_0(sK4(X1,o_0_0_xboole_0)) ),
    inference(resolution,[],[f284,f197])).

fof(f197,plain,(
    ! [X0] : m1_subset_1(sK4(X0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(superposition,[],[f112,f189])).

fof(f112,plain,(
    ! [X0,X1] : m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),X0,X1)
      & v1_funct_1(sK4(X0,X1))
      & v5_relat_1(sK4(X0,X1),X1)
      & v4_relat_1(sK4(X0,X1),X0)
      & v1_relat_1(sK4(X0,X1))
      & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK4(X0,X1),X0,X1)
        & v1_funct_1(sK4(X0,X1))
        & v5_relat_1(sK4(X0,X1),X1)
        & v4_relat_1(sK4(X0,X1),X0)
        & v1_relat_1(sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f116,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12998)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (12990)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (12982)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (12990)Refutation not found, incomplete strategy% (12990)------------------------------
% 0.21/0.51  % (12990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12980)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12985)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (12990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12990)Memory used [KB]: 10746
% 0.21/0.52  % (12990)Time elapsed: 0.098 s
% 0.21/0.52  % (12990)------------------------------
% 0.21/0.52  % (12990)------------------------------
% 0.21/0.52  % (12978)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (12998)Refutation not found, incomplete strategy% (12998)------------------------------
% 0.21/0.52  % (12998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12998)Memory used [KB]: 10746
% 0.21/0.52  % (12998)Time elapsed: 0.106 s
% 0.21/0.52  % (12998)------------------------------
% 0.21/0.52  % (12998)------------------------------
% 0.21/0.52  % (12979)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (12997)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  % (12994)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.53  % (12986)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.53  % (12974)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.54  % (13001)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.54  % (12987)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.54  % (12988)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.54  % (13001)Refutation not found, incomplete strategy% (13001)------------------------------
% 1.27/0.54  % (13001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (13001)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (13001)Memory used [KB]: 6268
% 1.27/0.54  % (13001)Time elapsed: 0.131 s
% 1.27/0.54  % (13001)------------------------------
% 1.27/0.54  % (13001)------------------------------
% 1.27/0.54  % (12991)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.54  % (13002)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.54  % (12975)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.55  % (12989)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.55  % (12977)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.55  % (13003)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.55  % (13003)Refutation not found, incomplete strategy% (13003)------------------------------
% 1.35/0.55  % (13003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (13003)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (13003)Memory used [KB]: 1663
% 1.35/0.55  % (13003)Time elapsed: 0.139 s
% 1.35/0.55  % (13003)------------------------------
% 1.35/0.55  % (13003)------------------------------
% 1.35/0.55  % (12993)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.35/0.55  % (12976)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.55  % (12995)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.55  % (12996)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.55  % (12981)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.55  % (12983)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.56  % (13000)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.56  % (12988)Refutation not found, incomplete strategy% (12988)------------------------------
% 1.35/0.56  % (12988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (12988)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (12988)Memory used [KB]: 1918
% 1.35/0.56  % (12988)Time elapsed: 0.154 s
% 1.35/0.56  % (12988)------------------------------
% 1.35/0.56  % (12988)------------------------------
% 1.35/0.56  % (12992)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.56  % (12999)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.57  % (12984)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.58  % (13000)Refutation not found, incomplete strategy% (13000)------------------------------
% 1.35/0.58  % (13000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (13000)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (13000)Memory used [KB]: 6396
% 1.35/0.58  % (13000)Time elapsed: 0.155 s
% 1.35/0.58  % (13000)------------------------------
% 1.35/0.58  % (13000)------------------------------
% 1.89/0.67  % (13007)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.26/0.68  % (13008)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.26/0.72  % (13010)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.26/0.72  % (13009)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.72/0.75  % (13022)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.72/0.76  % (12977)Refutation not found, incomplete strategy% (12977)------------------------------
% 2.72/0.76  % (12977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.76  % (13011)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.72/0.77  % (12977)Termination reason: Refutation not found, incomplete strategy
% 2.72/0.77  
% 2.72/0.77  % (12977)Memory used [KB]: 6268
% 2.72/0.77  % (12977)Time elapsed: 0.351 s
% 2.72/0.77  % (12977)------------------------------
% 2.72/0.77  % (12977)------------------------------
% 3.13/0.83  % (13011)Refutation not found, incomplete strategy% (13011)------------------------------
% 3.13/0.83  % (13011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.83  % (13011)Termination reason: Refutation not found, incomplete strategy
% 3.13/0.83  
% 3.13/0.83  % (13011)Memory used [KB]: 11001
% 3.13/0.83  % (13011)Time elapsed: 0.128 s
% 3.13/0.83  % (13011)------------------------------
% 3.13/0.83  % (13011)------------------------------
% 3.39/0.85  % (12976)Time limit reached!
% 3.39/0.85  % (12976)------------------------------
% 3.39/0.85  % (12976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.85  % (12976)Termination reason: Time limit
% 3.39/0.85  % (12976)Termination phase: Saturation
% 3.39/0.85  
% 3.39/0.85  % (12976)Memory used [KB]: 6780
% 3.39/0.85  % (12976)Time elapsed: 0.400 s
% 3.39/0.85  % (12976)------------------------------
% 3.39/0.85  % (12976)------------------------------
% 3.39/0.85  % (12980)Refutation found. Thanks to Tanya!
% 3.39/0.85  % SZS status Theorem for theBenchmark
% 3.39/0.85  % SZS output start Proof for theBenchmark
% 3.39/0.85  fof(f4734,plain,(
% 3.39/0.85    $false),
% 3.39/0.85    inference(avatar_sat_refutation,[],[f565,f1017,f1312,f1480,f1925,f1954,f2177,f2204,f3466,f3573,f3872,f4149,f4175,f4474,f4600])).
% 3.39/0.85  fof(f4600,plain,(
% 3.39/0.85    ~spl6_2 | ~spl6_4 | ~spl6_17 | ~spl6_43),
% 3.39/0.85    inference(avatar_contradiction_clause,[],[f4599])).
% 3.39/0.85  fof(f4599,plain,(
% 3.39/0.85    $false | (~spl6_2 | ~spl6_4 | ~spl6_17 | ~spl6_43)),
% 3.39/0.85    inference(subsumption_resolution,[],[f4598,f3676])).
% 3.39/0.85  fof(f3676,plain,(
% 3.39/0.85    o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_4 | ~spl6_43)),
% 3.39/0.85    inference(forward_demodulation,[],[f3675,f185])).
% 3.39/0.85  fof(f185,plain,(
% 3.39/0.85    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 3.39/0.85    inference(backward_demodulation,[],[f87,f182])).
% 3.39/0.85  fof(f182,plain,(
% 3.39/0.85    o_0_0_xboole_0 = k1_xboole_0),
% 3.39/0.85    inference(resolution,[],[f92,f85])).
% 3.39/0.85  fof(f85,plain,(
% 3.39/0.85    v1_xboole_0(o_0_0_xboole_0)),
% 3.39/0.85    inference(cnf_transformation,[],[f1])).
% 3.39/0.85  fof(f1,axiom,(
% 3.39/0.85    v1_xboole_0(o_0_0_xboole_0)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 3.39/0.85  fof(f92,plain,(
% 3.39/0.85    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.39/0.85    inference(cnf_transformation,[],[f35])).
% 3.39/0.85  fof(f35,plain,(
% 3.39/0.85    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.39/0.85    inference(ennf_transformation,[],[f2])).
% 3.39/0.85  fof(f2,axiom,(
% 3.39/0.85    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.39/0.85  fof(f87,plain,(
% 3.39/0.85    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.39/0.85    inference(cnf_transformation,[],[f18])).
% 3.39/0.85  fof(f18,axiom,(
% 3.39/0.85    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 3.39/0.85  fof(f3675,plain,(
% 3.39/0.85    k2_relat_1(o_0_0_xboole_0) != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_4 | ~spl6_43)),
% 3.39/0.85    inference(forward_demodulation,[],[f1512,f762])).
% 3.39/0.85  fof(f762,plain,(
% 3.39/0.85    o_0_0_xboole_0 = sK3 | ~spl6_4),
% 3.39/0.85    inference(resolution,[],[f282,f183])).
% 3.39/0.85  fof(f183,plain,(
% 3.39/0.85    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 3.39/0.85    inference(backward_demodulation,[],[f92,f182])).
% 3.39/0.85  fof(f282,plain,(
% 3.39/0.85    v1_xboole_0(sK3) | ~spl6_4),
% 3.39/0.85    inference(avatar_component_clause,[],[f280])).
% 3.39/0.85  fof(f280,plain,(
% 3.39/0.85    spl6_4 <=> v1_xboole_0(sK3)),
% 3.39/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.39/0.85  fof(f1512,plain,(
% 3.39/0.85    k2_relat_1(sK3) != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | ~spl6_43),
% 3.39/0.85    inference(backward_demodulation,[],[f620,f1491])).
% 3.39/0.85  fof(f1491,plain,(
% 3.39/0.85    o_0_0_xboole_0 = k1_funct_1(sK3,sK1) | ~spl6_43),
% 3.39/0.85    inference(resolution,[],[f1449,f183])).
% 3.39/0.85  fof(f1449,plain,(
% 3.39/0.85    v1_xboole_0(k1_funct_1(sK3,sK1)) | ~spl6_43),
% 3.39/0.85    inference(avatar_component_clause,[],[f1447])).
% 3.39/0.85  fof(f1447,plain,(
% 3.39/0.85    spl6_43 <=> v1_xboole_0(k1_funct_1(sK3,sK1))),
% 3.39/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 3.39/0.85  fof(f620,plain,(
% 3.39/0.85    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)),
% 3.39/0.85    inference(forward_demodulation,[],[f146,f443])).
% 3.39/0.85  fof(f443,plain,(
% 3.39/0.85    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3)),
% 3.39/0.85    inference(resolution,[],[f121,f147])).
% 3.39/0.85  fof(f147,plain,(
% 3.39/0.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.39/0.85    inference(definition_unfolding,[],[f82,f145])).
% 3.39/0.85  fof(f145,plain,(
% 3.39/0.85    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.39/0.85    inference(definition_unfolding,[],[f91,f144])).
% 3.39/0.85  fof(f144,plain,(
% 3.39/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.39/0.85    inference(definition_unfolding,[],[f99,f118])).
% 3.39/0.85  fof(f118,plain,(
% 3.39/0.85    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.39/0.85    inference(cnf_transformation,[],[f7])).
% 3.39/0.85  fof(f7,axiom,(
% 3.39/0.85    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.39/0.85  fof(f99,plain,(
% 3.39/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/0.85    inference(cnf_transformation,[],[f6])).
% 3.39/0.85  fof(f6,axiom,(
% 3.39/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.39/0.85  fof(f91,plain,(
% 3.39/0.85    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.39/0.85    inference(cnf_transformation,[],[f5])).
% 3.39/0.85  fof(f5,axiom,(
% 3.39/0.85    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.39/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.39/0.85  fof(f82,plain,(
% 3.39/0.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.39/0.85    inference(cnf_transformation,[],[f64])).
% 3.39/0.85  fof(f64,plain,(
% 3.39/0.85    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 3.39/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f63])).
% 3.39/0.85  fof(f63,plain,(
% 3.39/0.85    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 3.39/0.85    introduced(choice_axiom,[])).
% 3.39/0.86  fof(f34,plain,(
% 3.39/0.86    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.39/0.86    inference(flattening,[],[f33])).
% 3.39/0.86  fof(f33,plain,(
% 3.39/0.86    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.39/0.86    inference(ennf_transformation,[],[f32])).
% 3.39/0.86  fof(f32,negated_conjecture,(
% 3.39/0.86    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 3.39/0.86    inference(negated_conjecture,[],[f31])).
% 3.39/0.86  fof(f31,conjecture,(
% 3.39/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 3.39/0.86  fof(f121,plain,(
% 3.39/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f53])).
% 3.39/0.86  fof(f53,plain,(
% 3.39/0.86    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.86    inference(ennf_transformation,[],[f27])).
% 3.39/0.86  fof(f27,axiom,(
% 3.39/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.39/0.86  fof(f146,plain,(
% 3.39/0.86    k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1))),
% 3.39/0.86    inference(definition_unfolding,[],[f84,f145,f145])).
% 3.39/0.86  fof(f84,plain,(
% 3.39/0.86    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))),
% 3.39/0.86    inference(cnf_transformation,[],[f64])).
% 3.39/0.86  fof(f4598,plain,(
% 3.39/0.86    o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_2 | ~spl6_4 | ~spl6_17)),
% 3.39/0.86    inference(forward_demodulation,[],[f2563,f4104])).
% 3.39/0.86  fof(f4104,plain,(
% 3.39/0.86    ( ! [X0] : (o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)) ) | ~spl6_4),
% 3.39/0.86    inference(subsumption_resolution,[],[f4072,f85])).
% 3.39/0.86  fof(f4072,plain,(
% 3.39/0.86    ( ! [X0] : (~v1_xboole_0(o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)) ) | ~spl6_4),
% 3.39/0.86    inference(superposition,[],[f149,f3576])).
% 3.39/0.86  fof(f3576,plain,(
% 3.39/0.86    ( ! [X10] : (o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10)) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X10)) ) | ~spl6_4),
% 3.39/0.86    inference(forward_demodulation,[],[f3575,f762])).
% 3.39/0.86  fof(f3575,plain,(
% 3.39/0.86    ( ! [X10] : (o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10)) | o_0_0_xboole_0 = k1_funct_1(sK3,X10)) ) | ~spl6_4),
% 3.39/0.86    inference(forward_demodulation,[],[f3558,f498])).
% 3.39/0.86  fof(f498,plain,(
% 3.39/0.86    ( ! [X0] : (o_0_0_xboole_0 = k11_relat_1(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(forward_demodulation,[],[f493,f389])).
% 3.39/0.86  fof(f389,plain,(
% 3.39/0.86    ( ! [X0] : (o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(forward_demodulation,[],[f388,f185])).
% 3.39/0.86  fof(f388,plain,(
% 3.39/0.86    ( ! [X0] : (k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(forward_demodulation,[],[f295,f312])).
% 3.39/0.86  fof(f312,plain,(
% 3.39/0.86    ( ! [X2] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X2)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f307,f202])).
% 3.39/0.86  fof(f202,plain,(
% 3.39/0.86    v1_relat_1(o_0_0_xboole_0)),
% 3.39/0.86    inference(resolution,[],[f120,f184])).
% 3.39/0.86  fof(f184,plain,(
% 3.39/0.86    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 3.39/0.86    inference(backward_demodulation,[],[f90,f182])).
% 3.39/0.86  fof(f90,plain,(
% 3.39/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.39/0.86    inference(cnf_transformation,[],[f11])).
% 3.39/0.86  fof(f11,axiom,(
% 3.39/0.86    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.39/0.86  fof(f120,plain,(
% 3.39/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f52])).
% 3.39/0.86  fof(f52,plain,(
% 3.39/0.86    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.86    inference(ennf_transformation,[],[f23])).
% 3.39/0.86  fof(f23,axiom,(
% 3.39/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.39/0.86  fof(f307,plain,(
% 3.39/0.86    ( ! [X2] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X2) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 3.39/0.86    inference(resolution,[],[f106,f230])).
% 3.39/0.86  fof(f230,plain,(
% 3.39/0.86    ( ! [X0] : (v4_relat_1(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f229,f202])).
% 3.39/0.86  fof(f229,plain,(
% 3.39/0.86    ( ! [X0] : (v4_relat_1(o_0_0_xboole_0,X0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f227,f187])).
% 3.39/0.86  fof(f187,plain,(
% 3.39/0.86    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(backward_demodulation,[],[f89,f182])).
% 3.39/0.86  fof(f89,plain,(
% 3.39/0.86    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f3])).
% 3.39/0.86  fof(f3,axiom,(
% 3.39/0.86    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.39/0.86  fof(f227,plain,(
% 3.39/0.86    ( ! [X0] : (~r1_tarski(o_0_0_xboole_0,X0) | v4_relat_1(o_0_0_xboole_0,X0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 3.39/0.86    inference(superposition,[],[f103,f186])).
% 3.39/0.86  fof(f186,plain,(
% 3.39/0.86    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 3.39/0.86    inference(backward_demodulation,[],[f86,f182])).
% 3.39/0.86  fof(f86,plain,(
% 3.39/0.86    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.39/0.86    inference(cnf_transformation,[],[f18])).
% 3.39/0.86  fof(f103,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f66])).
% 3.39/0.86  fof(f66,plain,(
% 3.39/0.86    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.39/0.86    inference(nnf_transformation,[],[f43])).
% 3.39/0.86  fof(f43,plain,(
% 3.39/0.86    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.39/0.86    inference(ennf_transformation,[],[f15])).
% 3.39/0.86  fof(f15,axiom,(
% 3.39/0.86    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 3.39/0.86  fof(f106,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f49])).
% 3.39/0.86  fof(f49,plain,(
% 3.39/0.86    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.39/0.86    inference(flattening,[],[f48])).
% 3.39/0.86  fof(f48,plain,(
% 3.39/0.86    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.39/0.86    inference(ennf_transformation,[],[f17])).
% 3.39/0.86  fof(f17,axiom,(
% 3.39/0.86    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 3.39/0.86  fof(f295,plain,(
% 3.39/0.86    ( ! [X0] : (k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 3.39/0.86    inference(resolution,[],[f101,f202])).
% 3.39/0.86  fof(f101,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f42])).
% 3.39/0.86  fof(f42,plain,(
% 3.39/0.86    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.39/0.86    inference(ennf_transformation,[],[f16])).
% 3.39/0.86  fof(f16,axiom,(
% 3.39/0.86    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 3.39/0.86  fof(f493,plain,(
% 3.39/0.86    ( ! [X0] : (k11_relat_1(o_0_0_xboole_0,X0) = k9_relat_1(o_0_0_xboole_0,k2_enumset1(X0,X0,X0,X0))) )),
% 3.39/0.86    inference(resolution,[],[f150,f202])).
% 3.39/0.86  fof(f150,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.39/0.86    inference(definition_unfolding,[],[f93,f145])).
% 3.39/0.86  fof(f93,plain,(
% 3.39/0.86    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f36])).
% 3.39/0.86  fof(f36,plain,(
% 3.39/0.86    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.39/0.86    inference(ennf_transformation,[],[f14])).
% 3.39/0.86  fof(f14,axiom,(
% 3.39/0.86    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 3.39/0.86  fof(f3558,plain,(
% 3.39/0.86    ( ! [X10] : (k11_relat_1(o_0_0_xboole_0,X10) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10),k1_funct_1(o_0_0_xboole_0,X10)) | o_0_0_xboole_0 = k1_funct_1(sK3,X10)) ) | ~spl6_4),
% 3.39/0.86    inference(backward_demodulation,[],[f1740,f762])).
% 3.39/0.86  fof(f1740,plain,(
% 3.39/0.86    ( ! [X10] : (k11_relat_1(sK3,X10) = k2_enumset1(k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10)) | o_0_0_xboole_0 = k1_funct_1(sK3,X10)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f1730,f203])).
% 3.39/0.86  fof(f203,plain,(
% 3.39/0.86    v1_relat_1(sK3)),
% 3.39/0.86    inference(resolution,[],[f120,f147])).
% 3.39/0.86  fof(f1730,plain,(
% 3.39/0.86    ( ! [X10] : (k11_relat_1(sK3,X10) = k2_enumset1(k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10),k1_funct_1(sK3,X10)) | ~v1_relat_1(sK3) | o_0_0_xboole_0 = k1_funct_1(sK3,X10)) )),
% 3.39/0.86    inference(resolution,[],[f675,f80])).
% 3.39/0.86  fof(f80,plain,(
% 3.39/0.86    v1_funct_1(sK3)),
% 3.39/0.86    inference(cnf_transformation,[],[f64])).
% 3.39/0.86  fof(f675,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~v1_funct_1(X0) | k11_relat_1(X0,X1) = k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) | ~v1_relat_1(X0) | o_0_0_xboole_0 = k1_funct_1(X0,X1)) )),
% 3.39/0.86    inference(duplicate_literal_removal,[],[f671])).
% 3.39/0.86  fof(f671,plain,(
% 3.39/0.86    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | o_0_0_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.86    inference(resolution,[],[f151,f501])).
% 3.39/0.86  fof(f501,plain,(
% 3.39/0.86    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | o_0_0_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.86    inference(forward_demodulation,[],[f164,f182])).
% 3.39/0.86  fof(f164,plain,(
% 3.39/0.86    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.86    inference(equality_resolution,[],[f98])).
% 3.39/0.86  fof(f98,plain,(
% 3.39/0.86    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f65])).
% 3.39/0.86  fof(f65,plain,(
% 3.39/0.86    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/0.86    inference(nnf_transformation,[],[f40])).
% 3.39/0.86  fof(f40,plain,(
% 3.39/0.86    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/0.86    inference(flattening,[],[f39])).
% 3.39/0.86  fof(f39,plain,(
% 3.39/0.86    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.39/0.86    inference(ennf_transformation,[],[f20])).
% 3.39/0.86  fof(f20,axiom,(
% 3.39/0.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 3.39/0.86  fof(f151,plain,(
% 3.39/0.86    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.39/0.86    inference(definition_unfolding,[],[f104,f145])).
% 3.39/0.86  fof(f104,plain,(
% 3.39/0.86    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f45])).
% 3.39/0.86  fof(f45,plain,(
% 3.39/0.86    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.39/0.86    inference(flattening,[],[f44])).
% 3.39/0.86  fof(f44,plain,(
% 3.39/0.86    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.39/0.86    inference(ennf_transformation,[],[f21])).
% 3.39/0.86  fof(f21,axiom,(
% 3.39/0.86    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 3.39/0.86  fof(f149,plain,(
% 3.39/0.86    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 3.39/0.86    inference(definition_unfolding,[],[f88,f145])).
% 3.39/0.86  fof(f88,plain,(
% 3.39/0.86    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.39/0.86    inference(cnf_transformation,[],[f8])).
% 3.39/0.86  fof(f8,axiom,(
% 3.39/0.86    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 3.39/0.86  fof(f2563,plain,(
% 3.39/0.86    o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0)),k1_funct_1(o_0_0_xboole_0,k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0))) | (~spl6_2 | ~spl6_17)),
% 3.39/0.86    inference(resolution,[],[f634,f678])).
% 3.39/0.86  fof(f678,plain,(
% 3.39/0.86    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0))) ) | ~spl6_2),
% 3.39/0.86    inference(forward_demodulation,[],[f677,f498])).
% 3.39/0.86  fof(f677,plain,(
% 3.39/0.86    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0) | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0))) ) | ~spl6_2),
% 3.39/0.86    inference(subsumption_resolution,[],[f676,f202])).
% 3.39/0.86  fof(f676,plain,(
% 3.39/0.86    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0) | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0)) | ~v1_relat_1(o_0_0_xboole_0)) ) | ~spl6_2),
% 3.39/0.86    inference(subsumption_resolution,[],[f674,f266])).
% 3.39/0.86  fof(f266,plain,(
% 3.39/0.86    v1_funct_1(o_0_0_xboole_0) | ~spl6_2),
% 3.39/0.86    inference(avatar_component_clause,[],[f264])).
% 3.39/0.86  fof(f264,plain,(
% 3.39/0.86    spl6_2 <=> v1_funct_1(o_0_0_xboole_0)),
% 3.39/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.39/0.86  fof(f674,plain,(
% 3.39/0.86    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0) | k11_relat_1(o_0_0_xboole_0,X0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0),k1_funct_1(o_0_0_xboole_0,X0)) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 3.39/0.86    inference(superposition,[],[f151,f186])).
% 3.39/0.86  fof(f634,plain,(
% 3.39/0.86    r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0) | ~spl6_17),
% 3.39/0.86    inference(avatar_component_clause,[],[f632])).
% 3.39/0.86  fof(f632,plain,(
% 3.39/0.86    spl6_17 <=> r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0)),
% 3.39/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.39/0.86  fof(f4474,plain,(
% 3.39/0.86    ~spl6_4 | spl6_17 | ~spl6_22 | ~spl6_43 | ~spl6_169),
% 3.39/0.86    inference(avatar_contradiction_clause,[],[f4473])).
% 3.39/0.86  fof(f4473,plain,(
% 3.39/0.86    $false | (~spl6_4 | spl6_17 | ~spl6_22 | ~spl6_43 | ~spl6_169)),
% 3.39/0.86    inference(subsumption_resolution,[],[f4466,f3674])).
% 3.39/0.86  fof(f3674,plain,(
% 3.39/0.86    r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_4 | ~spl6_43)),
% 3.39/0.86    inference(forward_demodulation,[],[f3673,f185])).
% 3.39/0.86  fof(f3673,plain,(
% 3.39/0.86    r2_hidden(o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0)) | (~spl6_4 | ~spl6_43)),
% 3.39/0.86    inference(forward_demodulation,[],[f1513,f762])).
% 3.39/0.86  fof(f1513,plain,(
% 3.39/0.86    r2_hidden(o_0_0_xboole_0,k2_relat_1(sK3)) | ~spl6_43),
% 3.39/0.86    inference(backward_demodulation,[],[f1383,f1491])).
% 3.39/0.86  fof(f1383,plain,(
% 3.39/0.86    r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3))),
% 3.39/0.86    inference(resolution,[],[f728,f207])).
% 3.39/0.86  fof(f207,plain,(
% 3.39/0.86    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 3.39/0.86    inference(resolution,[],[f171,f170])).
% 3.39/0.86  fof(f170,plain,(
% 3.39/0.86    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 3.39/0.86    inference(equality_resolution,[],[f127])).
% 3.39/0.86  fof(f127,plain,(
% 3.39/0.86    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f76])).
% 3.39/0.86  fof(f76,plain,(
% 3.39/0.86    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.39/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).
% 3.39/0.86  fof(f75,plain,(
% 3.39/0.86    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 3.39/0.86    introduced(choice_axiom,[])).
% 3.39/0.86  fof(f74,plain,(
% 3.39/0.86    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.39/0.86    inference(rectify,[],[f73])).
% 3.39/0.86  fof(f73,plain,(
% 3.39/0.86    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.39/0.86    inference(flattening,[],[f72])).
% 3.39/0.86  fof(f72,plain,(
% 3.39/0.86    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.39/0.86    inference(nnf_transformation,[],[f61])).
% 3.39/0.86  fof(f61,plain,(
% 3.39/0.86    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.39/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.39/0.86  fof(f171,plain,(
% 3.39/0.86    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 3.39/0.86    inference(equality_resolution,[],[f154])).
% 3.39/0.86  fof(f154,plain,(
% 3.39/0.86    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.39/0.86    inference(definition_unfolding,[],[f132,f144])).
% 3.39/0.86  fof(f132,plain,(
% 3.39/0.86    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 3.39/0.86    inference(cnf_transformation,[],[f77])).
% 3.39/0.86  fof(f77,plain,(
% 3.39/0.86    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 3.39/0.86    inference(nnf_transformation,[],[f62])).
% 3.39/0.86  fof(f62,plain,(
% 3.39/0.86    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.39/0.86    inference(definition_folding,[],[f4,f61])).
% 3.39/0.86  fof(f4,axiom,(
% 3.39/0.86    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 3.39/0.86  fof(f728,plain,(
% 3.39/0.86    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f727,f80])).
% 3.39/0.86  fof(f727,plain,(
% 3.39/0.86    ( ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3)) | ~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f726,f148])).
% 3.39/0.86  fof(f148,plain,(
% 3.39/0.86    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.39/0.86    inference(definition_unfolding,[],[f81,f145])).
% 3.39/0.86  fof(f81,plain,(
% 3.39/0.86    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 3.39/0.86    inference(cnf_transformation,[],[f64])).
% 3.39/0.86  fof(f726,plain,(
% 3.39/0.86    ( ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3)) | ~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | ~v1_funct_1(sK3)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f725,f147])).
% 3.39/0.86  fof(f725,plain,(
% 3.39/0.86    ( ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3)) | ~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | ~v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | ~v1_funct_1(sK3)) )),
% 3.39/0.86    inference(subsumption_resolution,[],[f704,f188])).
% 3.39/0.86  fof(f188,plain,(
% 3.39/0.86    o_0_0_xboole_0 != sK2),
% 3.39/0.86    inference(backward_demodulation,[],[f83,f182])).
% 3.39/0.86  fof(f83,plain,(
% 3.39/0.86    k1_xboole_0 != sK2),
% 3.39/0.86    inference(cnf_transformation,[],[f64])).
% 3.39/0.86  fof(f704,plain,(
% 3.39/0.86    ( ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3)) | o_0_0_xboole_0 = sK2 | ~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) | ~v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | ~v1_funct_1(sK3)) )),
% 3.39/0.86    inference(superposition,[],[f699,f443])).
% 3.39/0.86  fof(f699,plain,(
% 3.39/0.86    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/0.86    inference(forward_demodulation,[],[f134,f182])).
% 3.39/0.86  fof(f134,plain,(
% 3.39/0.86    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/0.86    inference(cnf_transformation,[],[f59])).
% 3.39/0.86  fof(f59,plain,(
% 3.39/0.86    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.39/0.86    inference(flattening,[],[f58])).
% 3.39/0.86  fof(f58,plain,(
% 3.39/0.86    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.39/0.86    inference(ennf_transformation,[],[f30])).
% 3.39/0.86  fof(f30,axiom,(
% 3.39/0.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.39/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 3.39/0.86  fof(f4466,plain,(
% 3.39/0.86    ~r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_4 | spl6_17 | ~spl6_22 | ~spl6_169)),
% 3.39/0.86    inference(backward_demodulation,[],[f4344,f4351])).
% 3.39/0.86  fof(f4351,plain,(
% 3.39/0.86    o_0_0_xboole_0 = k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_22 | ~spl6_169)),
% 3.39/0.86    inference(resolution,[],[f4345,f183])).
% 3.39/0.86  fof(f4345,plain,(
% 3.39/0.86    v1_xboole_0(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0)) | (~spl6_22 | ~spl6_169)),
% 3.39/0.86    inference(forward_demodulation,[],[f4174,f1012])).
% 3.39/0.86  fof(f1012,plain,(
% 3.39/0.86    o_0_0_xboole_0 = sK1 | ~spl6_22),
% 3.39/0.86    inference(avatar_component_clause,[],[f1010])).
% 3.39/0.86  fof(f1010,plain,(
% 3.39/0.86    spl6_22 <=> o_0_0_xboole_0 = sK1),
% 3.39/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 3.39/0.86  fof(f4174,plain,(
% 3.39/0.86    v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0)) | ~spl6_169),
% 3.39/0.86    inference(avatar_component_clause,[],[f4172])).
% 3.39/0.86  fof(f4172,plain,(
% 3.39/0.86    spl6_169 <=> v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0))),
% 3.39/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).
% 3.39/0.86  fof(f4344,plain,(
% 3.39/0.86    ~r2_hidden(k4_tarski(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) | (~spl6_4 | spl6_17)),
% 3.39/0.86    inference(forward_demodulation,[],[f4343,f185])).
% 3.39/0.86  fof(f4343,plain,(
% 3.39/0.86    ~r2_hidden(k4_tarski(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) | (~spl6_4 | spl6_17)),
% 3.39/0.86    inference(forward_demodulation,[],[f633,f762])).
% 3.39/0.86  fof(f633,plain,(
% 3.39/0.86    ~r2_hidden(k4_tarski(k2_relat_1(sK3),o_0_0_xboole_0),o_0_0_xboole_0) | spl6_17),
% 3.39/0.86    inference(avatar_component_clause,[],[f632])).
% 3.39/0.86  fof(f4175,plain,(
% 3.39/0.86    ~spl6_139 | spl6_169 | ~spl6_2 | ~spl6_4),
% 3.39/0.86    inference(avatar_split_clause,[],[f4038,f280,f264,f4172,f3666])).
% 3.39/0.86  fof(f3666,plain,(
% 3.39/0.86    spl6_139 <=> r2_hidden(sK1,o_0_0_xboole_0)),
% 3.39/0.86    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).
% 3.39/0.86  fof(f4038,plain,(
% 3.39/0.86    v1_xboole_0(k4_tarski(sK1,o_0_0_xboole_0)) | ~r2_hidden(sK1,o_0_0_xboole_0) | (~spl6_2 | ~spl6_4)),
% 3.39/0.86    inference(superposition,[],[f1822,f4029])).
% 3.39/0.86  fof(f4029,plain,(
% 3.39/0.86    o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,sK1) | ~spl6_4),
% 3.39/0.86    inference(forward_demodulation,[],[f3490,f762])).
% 3.39/0.87  fof(f3490,plain,(
% 3.39/0.87    o_0_0_xboole_0 = k1_funct_1(sK3,sK1)),
% 3.39/0.87    inference(global_subsumption,[],[f499,f3413])).
% 3.39/0.87  fof(f3413,plain,(
% 3.39/0.87    k2_relat_1(sK3) != k11_relat_1(sK3,sK1) | o_0_0_xboole_0 = k1_funct_1(sK3,sK1)),
% 3.39/0.87    inference(superposition,[],[f620,f1740])).
% 3.39/0.87  fof(f499,plain,(
% 3.39/0.87    k2_relat_1(sK3) = k11_relat_1(sK3,sK1)),
% 3.39/0.87    inference(superposition,[],[f496,f365])).
% 3.39/0.87  fof(f365,plain,(
% 3.39/0.87    k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3)),
% 3.39/0.87    inference(superposition,[],[f298,f313])).
% 3.39/0.87  fof(f313,plain,(
% 3.39/0.87    sK3 = k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.39/0.87    inference(subsumption_resolution,[],[f308,f203])).
% 3.39/0.87  fof(f308,plain,(
% 3.39/0.87    sK3 = k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_relat_1(sK3)),
% 3.39/0.87    inference(resolution,[],[f106,f238])).
% 3.39/0.87  fof(f238,plain,(
% 3.39/0.87    v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.39/0.87    inference(resolution,[],[f123,f147])).
% 3.39/0.87  fof(f123,plain,(
% 3.39/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.39/0.87    inference(cnf_transformation,[],[f55])).
% 3.39/0.87  fof(f55,plain,(
% 3.39/0.87    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.87    inference(ennf_transformation,[],[f24])).
% 3.39/0.87  fof(f24,axiom,(
% 3.39/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.39/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.39/0.87  fof(f298,plain,(
% 3.39/0.87    ( ! [X5] : (k2_relat_1(k7_relat_1(sK3,X5)) = k9_relat_1(sK3,X5)) )),
% 3.39/0.87    inference(resolution,[],[f101,f203])).
% 3.39/0.87  fof(f496,plain,(
% 3.39/0.87    ( ! [X6] : (k11_relat_1(sK3,X6) = k9_relat_1(sK3,k2_enumset1(X6,X6,X6,X6))) )),
% 3.39/0.87    inference(resolution,[],[f150,f203])).
% 3.39/0.87  fof(f1822,plain,(
% 3.39/0.87    ( ! [X53] : (v1_xboole_0(k4_tarski(X53,k1_funct_1(o_0_0_xboole_0,X53))) | ~r2_hidden(X53,o_0_0_xboole_0)) ) | ~spl6_2),
% 3.39/0.87    inference(resolution,[],[f574,f284])).
% 3.39/0.87  fof(f284,plain,(
% 3.39/0.87    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0)) | v1_xboole_0(X1)) )),
% 3.39/0.87    inference(subsumption_resolution,[],[f273,f85])).
% 3.39/0.87  fof(f273,plain,(
% 3.39/0.87    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0)) | v1_xboole_0(X1) | ~v1_xboole_0(o_0_0_xboole_0)) )),
% 3.39/0.87    inference(superposition,[],[f100,f189])).
% 3.39/0.87  fof(f189,plain,(
% 3.39/0.87    ( ! [X0] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)) )),
% 3.39/0.87    inference(forward_demodulation,[],[f167,f182])).
% 3.39/0.87  fof(f167,plain,(
% 3.39/0.87    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.39/0.87    inference(equality_resolution,[],[f111])).
% 3.39/0.87  fof(f111,plain,(
% 3.39/0.87    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.39/0.87    inference(cnf_transformation,[],[f69])).
% 3.39/0.87  fof(f69,plain,(
% 3.39/0.87    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.39/0.87    inference(flattening,[],[f68])).
% 3.39/0.87  fof(f68,plain,(
% 3.39/0.87    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.39/0.87    inference(nnf_transformation,[],[f9])).
% 3.39/0.87  fof(f9,axiom,(
% 3.39/0.87    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.39/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.39/0.87  fof(f100,plain,(
% 3.39/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 3.39/0.87    inference(cnf_transformation,[],[f41])).
% 3.39/0.87  fof(f41,plain,(
% 3.39/0.87    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.39/0.87    inference(ennf_transformation,[],[f25])).
% 3.39/0.87  fof(f25,axiom,(
% 3.39/0.87    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.39/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 3.39/0.87  fof(f574,plain,(
% 3.39/0.87    ( ! [X4,X3] : (m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4) | ~r2_hidden(X3,o_0_0_xboole_0)) ) | ~spl6_2),
% 3.39/0.87    inference(forward_demodulation,[],[f573,f186])).
% 3.39/0.87  fof(f573,plain,(
% 3.39/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4)) ) | ~spl6_2),
% 3.39/0.87    inference(subsumption_resolution,[],[f572,f202])).
% 3.39/0.87  fof(f572,plain,(
% 3.39/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) | ~v1_relat_1(o_0_0_xboole_0) | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4)) ) | ~spl6_2),
% 3.39/0.87    inference(subsumption_resolution,[],[f569,f266])).
% 3.39/0.87  fof(f569,plain,(
% 3.39/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | m1_subset_1(k4_tarski(X3,k1_funct_1(o_0_0_xboole_0,X3)),X4)) )),
% 3.39/0.87    inference(resolution,[],[f166,f341])).
% 3.39/0.87  fof(f341,plain,(
% 3.39/0.87    ( ! [X4,X3] : (~r2_hidden(X3,o_0_0_xboole_0) | m1_subset_1(X3,X4)) )),
% 3.39/0.87    inference(resolution,[],[f125,f184])).
% 3.39/0.87  fof(f125,plain,(
% 3.39/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.39/0.87    inference(cnf_transformation,[],[f57])).
% 3.39/0.87  fof(f57,plain,(
% 3.39/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.39/0.87    inference(flattening,[],[f56])).
% 3.39/0.87  fof(f56,plain,(
% 3.39/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.39/0.87    inference(ennf_transformation,[],[f13])).
% 3.39/0.87  fof(f13,axiom,(
% 3.39/0.87    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.39/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 3.39/0.87  fof(f166,plain,(
% 3.39/0.87    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.87    inference(equality_resolution,[],[f95])).
% 3.39/0.87  fof(f95,plain,(
% 3.39/0.87    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.87    inference(cnf_transformation,[],[f65])).
% 3.39/0.87  fof(f4149,plain,(
% 3.39/0.87    ~spl6_2 | ~spl6_4 | spl6_23 | ~spl6_43),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f4146])).
% 3.39/0.87  fof(f4146,plain,(
% 3.39/0.87    $false | (~spl6_2 | ~spl6_4 | spl6_23 | ~spl6_43)),
% 3.39/0.87    inference(resolution,[],[f4131,f3674])).
% 3.39/0.87  fof(f4131,plain,(
% 3.39/0.87    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) ) | (~spl6_2 | ~spl6_4 | spl6_23)),
% 3.39/0.87    inference(subsumption_resolution,[],[f4121,f1016])).
% 3.39/0.87  fof(f1016,plain,(
% 3.39/0.87    o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | spl6_23),
% 3.39/0.87    inference(avatar_component_clause,[],[f1014])).
% 3.39/0.87  fof(f1014,plain,(
% 3.39/0.87    spl6_23 <=> o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),
% 3.39/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 3.39/0.87  fof(f4121,plain,(
% 3.39/0.87    ( ! [X0] : (o_0_0_xboole_0 = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | ~r2_hidden(X0,o_0_0_xboole_0)) ) | (~spl6_2 | ~spl6_4)),
% 3.39/0.87    inference(backward_demodulation,[],[f678,f4104])).
% 3.39/0.87  fof(f3872,plain,(
% 3.39/0.87    ~spl6_4 | ~spl6_22 | ~spl6_43 | spl6_139),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f3871])).
% 3.39/0.87  fof(f3871,plain,(
% 3.39/0.87    $false | (~spl6_4 | ~spl6_22 | ~spl6_43 | spl6_139)),
% 3.39/0.87    inference(subsumption_resolution,[],[f3870,f3674])).
% 3.39/0.87  fof(f3870,plain,(
% 3.39/0.87    ~r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_22 | spl6_139)),
% 3.39/0.87    inference(forward_demodulation,[],[f3668,f1012])).
% 3.39/0.87  fof(f3668,plain,(
% 3.39/0.87    ~r2_hidden(sK1,o_0_0_xboole_0) | spl6_139),
% 3.39/0.87    inference(avatar_component_clause,[],[f3666])).
% 3.39/0.87  fof(f3573,plain,(
% 3.39/0.87    ~spl6_4 | spl6_47),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f3572])).
% 3.39/0.87  fof(f3572,plain,(
% 3.39/0.87    $false | (~spl6_4 | spl6_47)),
% 3.39/0.87    inference(subsumption_resolution,[],[f3571,f187])).
% 3.39/0.87  fof(f3571,plain,(
% 3.39/0.87    ~r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) | (~spl6_4 | spl6_47)),
% 3.39/0.87    inference(forward_demodulation,[],[f3556,f185])).
% 3.39/0.87  fof(f3556,plain,(
% 3.39/0.87    ~r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) | (~spl6_4 | spl6_47)),
% 3.39/0.87    inference(backward_demodulation,[],[f1465,f762])).
% 3.39/0.87  fof(f1465,plain,(
% 3.39/0.87    ~r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) | spl6_47),
% 3.39/0.87    inference(avatar_component_clause,[],[f1463])).
% 3.39/0.87  fof(f1463,plain,(
% 3.39/0.87    spl6_47 <=> r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))),
% 3.39/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 3.39/0.87  fof(f3466,plain,(
% 3.39/0.87    spl6_43 | ~spl6_66),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f3465])).
% 3.39/0.87  fof(f3465,plain,(
% 3.39/0.87    $false | (spl6_43 | ~spl6_66)),
% 3.39/0.87    inference(subsumption_resolution,[],[f3452,f85])).
% 3.39/0.87  fof(f3452,plain,(
% 3.39/0.87    ~v1_xboole_0(o_0_0_xboole_0) | (spl6_43 | ~spl6_66)),
% 3.39/0.87    inference(backward_demodulation,[],[f1448,f3447])).
% 3.39/0.87  fof(f3447,plain,(
% 3.39/0.87    o_0_0_xboole_0 = k1_funct_1(sK3,sK1) | ~spl6_66),
% 3.39/0.87    inference(subsumption_resolution,[],[f3413,f3076])).
% 3.39/0.87  fof(f3076,plain,(
% 3.39/0.87    k2_relat_1(sK3) = k11_relat_1(sK3,sK1) | ~spl6_66),
% 3.39/0.87    inference(forward_demodulation,[],[f3047,f2116])).
% 3.39/0.87  fof(f2116,plain,(
% 3.39/0.87    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) | ~spl6_66),
% 3.39/0.87    inference(backward_demodulation,[],[f365,f1924])).
% 3.39/0.87  fof(f1924,plain,(
% 3.39/0.87    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | ~spl6_66),
% 3.39/0.87    inference(avatar_component_clause,[],[f1922])).
% 3.39/0.87  fof(f1922,plain,(
% 3.39/0.87    spl6_66 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)),
% 3.39/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 3.39/0.87  fof(f3047,plain,(
% 3.39/0.87    k11_relat_1(sK3,sK1) = k9_relat_1(sK3,k1_relat_1(sK3)) | ~spl6_66),
% 3.39/0.87    inference(superposition,[],[f496,f1924])).
% 3.39/0.87  fof(f1448,plain,(
% 3.39/0.87    ~v1_xboole_0(k1_funct_1(sK3,sK1)) | spl6_43),
% 3.39/0.87    inference(avatar_component_clause,[],[f1447])).
% 3.39/0.87  fof(f2204,plain,(
% 3.39/0.87    spl6_4 | ~spl6_36),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f2203])).
% 3.39/0.87  fof(f2203,plain,(
% 3.39/0.87    $false | (spl6_4 | ~spl6_36)),
% 3.39/0.87    inference(subsumption_resolution,[],[f2197,f281])).
% 3.39/0.87  fof(f281,plain,(
% 3.39/0.87    ~v1_xboole_0(sK3) | spl6_4),
% 3.39/0.87    inference(avatar_component_clause,[],[f280])).
% 3.39/0.87  fof(f2197,plain,(
% 3.39/0.87    v1_xboole_0(sK3) | ~spl6_36),
% 3.39/0.87    inference(resolution,[],[f1311,f284])).
% 3.39/0.87  fof(f1311,plain,(
% 3.39/0.87    m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) | ~spl6_36),
% 3.39/0.87    inference(avatar_component_clause,[],[f1309])).
% 3.39/0.87  fof(f1309,plain,(
% 3.39/0.87    spl6_36 <=> m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))),
% 3.39/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 3.39/0.87  fof(f2177,plain,(
% 3.39/0.87    ~spl6_43 | ~spl6_66),
% 3.39/0.87    inference(avatar_contradiction_clause,[],[f2176])).
% 3.39/0.87  fof(f2176,plain,(
% 3.39/0.87    $false | (~spl6_43 | ~spl6_66)),
% 3.39/0.87    inference(subsumption_resolution,[],[f2175,f1512])).
% 3.39/0.87  fof(f2175,plain,(
% 3.39/0.87    k2_relat_1(sK3) = k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl6_43 | ~spl6_66)),
% 3.39/0.87    inference(forward_demodulation,[],[f2174,f1491])).
% 3.39/0.87  fof(f2174,plain,(
% 3.39/0.87    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3) | ~spl6_66),
% 3.39/0.87    inference(forward_demodulation,[],[f2173,f499])).
% 3.39/0.87  fof(f2173,plain,(
% 3.39/0.87    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) | ~spl6_66),
% 3.39/0.87    inference(subsumption_resolution,[],[f2172,f203])).
% 3.39/0.87  fof(f2172,plain,(
% 3.39/0.87    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | ~spl6_66),
% 3.39/0.87    inference(subsumption_resolution,[],[f2162,f80])).
% 3.39/0.88  fof(f2162,plain,(
% 3.39/0.88    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_66),
% 3.39/0.88    inference(resolution,[],[f2132,f151])).
% 3.39/0.88  fof(f2132,plain,(
% 3.39/0.88    r2_hidden(sK1,k1_relat_1(sK3)) | ~spl6_66),
% 3.39/0.88    inference(superposition,[],[f207,f1924])).
% 3.39/0.88  fof(f1954,plain,(
% 3.39/0.88    spl6_35 | ~spl6_65),
% 3.39/0.88    inference(avatar_contradiction_clause,[],[f1953])).
% 3.39/0.88  fof(f1953,plain,(
% 3.39/0.88    $false | (spl6_35 | ~spl6_65)),
% 3.39/0.88    inference(subsumption_resolution,[],[f1931,f187])).
% 3.39/0.88  fof(f1931,plain,(
% 3.39/0.88    ~r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) | (spl6_35 | ~spl6_65)),
% 3.39/0.88    inference(backward_demodulation,[],[f1307,f1920])).
% 3.39/0.88  fof(f1920,plain,(
% 3.39/0.88    o_0_0_xboole_0 = k1_relat_1(sK3) | ~spl6_65),
% 3.39/0.88    inference(avatar_component_clause,[],[f1918])).
% 3.39/0.88  fof(f1918,plain,(
% 3.39/0.88    spl6_65 <=> o_0_0_xboole_0 = k1_relat_1(sK3)),
% 3.39/0.88    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 3.39/0.88  fof(f1307,plain,(
% 3.39/0.88    ~r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0) | spl6_35),
% 3.39/0.88    inference(avatar_component_clause,[],[f1305])).
% 3.39/0.88  fof(f1305,plain,(
% 3.39/0.88    spl6_35 <=> r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)),
% 3.39/0.88    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 3.39/0.88  fof(f1925,plain,(
% 3.39/0.88    spl6_65 | spl6_66),
% 3.39/0.88    inference(avatar_split_clause,[],[f1916,f1922,f1918])).
% 3.39/0.88  fof(f1916,plain,(
% 3.39/0.88    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | o_0_0_xboole_0 = k1_relat_1(sK3)),
% 3.39/0.88    inference(subsumption_resolution,[],[f1915,f203])).
% 3.39/0.88  fof(f1915,plain,(
% 3.39/0.88    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | o_0_0_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 3.39/0.88    inference(duplicate_literal_removal,[],[f1908])).
% 3.39/0.88  fof(f1908,plain,(
% 3.39/0.88    k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | o_0_0_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 3.39/0.88    inference(resolution,[],[f836,f238])).
% 3.39/0.88  fof(f836,plain,(
% 3.39/0.88    ( ! [X30,X28,X31,X29] : (~v4_relat_1(X31,k2_enumset1(X28,X28,X29,X30)) | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X30) | k1_relat_1(X31) = k2_enumset1(X29,X29,X29,X30) | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X29) | k1_relat_1(X31) = k2_enumset1(X30,X30,X30,X30) | k1_relat_1(X31) = k2_enumset1(X29,X29,X29,X29) | k1_relat_1(X31) = k2_enumset1(X28,X28,X28,X28) | o_0_0_xboole_0 = k1_relat_1(X31) | k2_enumset1(X28,X28,X29,X30) = k1_relat_1(X31) | ~v1_relat_1(X31)) )),
% 3.39/0.88    inference(resolution,[],[f759,f102])).
% 3.39/0.88  fof(f102,plain,(
% 3.39/0.88    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/0.88    inference(cnf_transformation,[],[f66])).
% 3.39/0.88  fof(f759,plain,(
% 3.39/0.88    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | o_0_0_xboole_0 = X3) )),
% 3.39/0.88    inference(forward_demodulation,[],[f163,f182])).
% 3.39/0.88  fof(f163,plain,(
% 3.39/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 3.39/0.88    inference(definition_unfolding,[],[f135,f118,f144,f144,f144,f145,f145,f145,f118])).
% 3.39/0.88  fof(f135,plain,(
% 3.39/0.88    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 3.39/0.88    inference(cnf_transformation,[],[f79])).
% 3.39/0.88  fof(f79,plain,(
% 3.39/0.88    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.39/0.88    inference(flattening,[],[f78])).
% 3.39/0.88  fof(f78,plain,(
% 3.39/0.88    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.39/0.88    inference(nnf_transformation,[],[f60])).
% 3.39/0.88  fof(f60,plain,(
% 3.39/0.88    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 3.39/0.88    inference(ennf_transformation,[],[f10])).
% 3.39/0.88  fof(f10,axiom,(
% 3.39/0.88    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 3.39/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 3.39/0.88  fof(f1480,plain,(
% 3.39/0.88    spl6_43 | ~spl6_47),
% 3.39/0.88    inference(avatar_split_clause,[],[f1435,f1463,f1447])).
% 3.39/0.88  fof(f1435,plain,(
% 3.39/0.88    ~r1_tarski(k2_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) | v1_xboole_0(k1_funct_1(sK3,sK1))),
% 3.39/0.88    inference(resolution,[],[f1401,f284])).
% 3.39/0.88  fof(f1401,plain,(
% 3.39/0.88    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,sK1),X0) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 3.39/0.88    inference(resolution,[],[f1383,f340])).
% 3.39/0.88  fof(f340,plain,(
% 3.39/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~r1_tarski(X2,X1)) )),
% 3.39/0.88    inference(resolution,[],[f125,f108])).
% 3.39/0.88  fof(f108,plain,(
% 3.39/0.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.39/0.88    inference(cnf_transformation,[],[f67])).
% 3.39/0.88  fof(f67,plain,(
% 3.39/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.39/0.88    inference(nnf_transformation,[],[f12])).
% 3.39/0.88  fof(f12,axiom,(
% 3.39/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.39/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.39/0.88  fof(f1312,plain,(
% 3.39/0.88    ~spl6_35 | spl6_36),
% 3.39/0.88    inference(avatar_split_clause,[],[f1303,f1309,f1305])).
% 3.39/0.88  fof(f1303,plain,(
% 3.39/0.88    m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) | ~r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)),
% 3.39/0.88    inference(subsumption_resolution,[],[f1299,f203])).
% 3.39/0.88  fof(f1299,plain,(
% 3.39/0.88    m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) | ~r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0) | ~v1_relat_1(sK3)),
% 3.39/0.88    inference(resolution,[],[f471,f603])).
% 3.39/0.88  fof(f603,plain,(
% 3.39/0.88    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X3),X2) | m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0)) | ~r1_tarski(k1_relat_1(X3),o_0_0_xboole_0) | ~v1_relat_1(X3)) )),
% 3.39/0.88    inference(superposition,[],[f119,f190])).
% 3.39/0.88  fof(f190,plain,(
% 3.39/0.88    ( ! [X1] : (o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)) )),
% 3.39/0.88    inference(forward_demodulation,[],[f168,f182])).
% 3.39/0.88  fof(f168,plain,(
% 3.39/0.88    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.39/0.88    inference(equality_resolution,[],[f110])).
% 3.39/0.88  fof(f110,plain,(
% 3.39/0.88    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.39/0.88    inference(cnf_transformation,[],[f69])).
% 3.39/0.88  fof(f119,plain,(
% 3.39/0.88    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.39/0.88    inference(cnf_transformation,[],[f51])).
% 3.39/0.88  fof(f51,plain,(
% 3.39/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.39/0.88    inference(flattening,[],[f50])).
% 3.39/0.88  fof(f50,plain,(
% 3.39/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.39/0.88    inference(ennf_transformation,[],[f28])).
% 3.39/0.88  fof(f28,axiom,(
% 3.39/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.39/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 3.39/0.88  fof(f471,plain,(
% 3.39/0.88    r1_tarski(k2_relat_1(sK3),sK2)),
% 3.39/0.88    inference(resolution,[],[f468,f107])).
% 3.39/0.88  fof(f107,plain,(
% 3.39/0.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.39/0.88    inference(cnf_transformation,[],[f67])).
% 3.39/0.88  fof(f468,plain,(
% 3.39/0.88    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 3.39/0.88    inference(subsumption_resolution,[],[f462,f147])).
% 3.39/0.88  fof(f462,plain,(
% 3.39/0.88    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.39/0.88    inference(superposition,[],[f122,f443])).
% 3.39/0.88  fof(f122,plain,(
% 3.39/0.88    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/0.88    inference(cnf_transformation,[],[f54])).
% 3.39/0.88  fof(f54,plain,(
% 3.39/0.88    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.88    inference(ennf_transformation,[],[f26])).
% 3.39/0.88  fof(f26,axiom,(
% 3.39/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.39/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 3.39/0.88  fof(f1017,plain,(
% 3.39/0.88    spl6_22 | ~spl6_23 | ~spl6_2 | ~spl6_4),
% 3.39/0.88    inference(avatar_split_clause,[],[f1006,f280,f264,f1014,f1010])).
% 3.39/0.88  fof(f1006,plain,(
% 3.39/0.88    o_0_0_xboole_0 != k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | o_0_0_xboole_0 = sK1 | (~spl6_2 | ~spl6_4)),
% 3.39/0.88    inference(superposition,[],[f798,f623])).
% 3.39/0.88  fof(f623,plain,(
% 3.39/0.88    ( ! [X5] : (o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X5) | o_0_0_xboole_0 = X5) ) | ~spl6_2),
% 3.39/0.88    inference(resolution,[],[f547,f183])).
% 3.39/0.88  fof(f547,plain,(
% 3.39/0.88    ( ! [X20] : (v1_xboole_0(X20) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X20)) ) | ~spl6_2),
% 3.39/0.88    inference(resolution,[],[f534,f284])).
% 3.39/0.88  fof(f534,plain,(
% 3.39/0.88    ( ! [X0,X1] : (m1_subset_1(X0,X1) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)) ) | ~spl6_2),
% 3.39/0.88    inference(resolution,[],[f533,f341])).
% 3.39/0.88  fof(f533,plain,(
% 3.39/0.88    ( ! [X0] : (r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)) ) | ~spl6_2),
% 3.39/0.88    inference(subsumption_resolution,[],[f532,f202])).
% 3.39/0.88  fof(f532,plain,(
% 3.39/0.88    ( ! [X0] : (r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0) | ~v1_relat_1(o_0_0_xboole_0)) ) | ~spl6_2),
% 3.39/0.88    inference(subsumption_resolution,[],[f531,f266])).
% 3.39/0.88  fof(f531,plain,(
% 3.39/0.88    ( ! [X0] : (r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 3.39/0.88    inference(superposition,[],[f501,f186])).
% 3.39/0.88  fof(f798,plain,(
% 3.39/0.88    o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) | ~spl6_4),
% 3.39/0.88    inference(forward_demodulation,[],[f783,f185])).
% 3.39/0.88  fof(f783,plain,(
% 3.39/0.88    k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) | ~spl6_4),
% 3.39/0.88    inference(backward_demodulation,[],[f620,f762])).
% 3.39/0.88  fof(f565,plain,(
% 3.39/0.88    spl6_2),
% 3.39/0.88    inference(avatar_contradiction_clause,[],[f564])).
% 3.39/0.88  fof(f564,plain,(
% 3.39/0.88    $false | spl6_2),
% 3.39/0.88    inference(subsumption_resolution,[],[f329,f265])).
% 3.39/0.88  fof(f265,plain,(
% 3.39/0.88    ~v1_funct_1(o_0_0_xboole_0) | spl6_2),
% 3.39/0.88    inference(avatar_component_clause,[],[f264])).
% 3.39/0.88  fof(f329,plain,(
% 3.39/0.88    v1_funct_1(o_0_0_xboole_0)),
% 3.39/0.88    inference(superposition,[],[f116,f304])).
% 3.39/0.88  fof(f304,plain,(
% 3.39/0.88    ( ! [X0] : (o_0_0_xboole_0 = sK4(X0,o_0_0_xboole_0)) )),
% 3.39/0.88    inference(resolution,[],[f302,f183])).
% 3.39/0.88  fof(f302,plain,(
% 3.39/0.88    ( ! [X1] : (v1_xboole_0(sK4(X1,o_0_0_xboole_0))) )),
% 3.39/0.88    inference(resolution,[],[f284,f197])).
% 3.39/0.88  fof(f197,plain,(
% 3.39/0.88    ( ! [X0] : (m1_subset_1(sK4(X0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))) )),
% 3.39/0.88    inference(superposition,[],[f112,f189])).
% 3.39/0.88  fof(f112,plain,(
% 3.39/0.88    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/0.88    inference(cnf_transformation,[],[f71])).
% 3.39/0.88  fof(f71,plain,(
% 3.39/0.88    ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f70])).
% 3.39/0.88  fof(f70,plain,(
% 3.39/0.88    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.39/0.88    introduced(choice_axiom,[])).
% 3.39/0.88  fof(f29,axiom,(
% 3.39/0.88    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 3.39/0.88  fof(f116,plain,(
% 3.39/0.88    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 3.39/0.88    inference(cnf_transformation,[],[f71])).
% 3.39/0.88  % SZS output end Proof for theBenchmark
% 3.39/0.88  % (12980)------------------------------
% 3.39/0.88  % (12980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.88  % (12980)Termination reason: Refutation
% 3.39/0.88  
% 3.39/0.88  % (12980)Memory used [KB]: 13432
% 3.39/0.88  % (12980)Time elapsed: 0.430 s
% 3.39/0.88  % (12980)------------------------------
% 3.39/0.88  % (12980)------------------------------
% 3.39/0.88  % (12973)Success in time 0.509 s
%------------------------------------------------------------------------------
