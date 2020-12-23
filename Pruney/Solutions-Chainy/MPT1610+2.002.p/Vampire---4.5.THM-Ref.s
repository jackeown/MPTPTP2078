%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 225 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  218 ( 536 expanded)
%              Number of equality atoms :  113 ( 303 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(superposition,[],[f95,f268])).

fof(f268,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(subsumption_resolution,[],[f267,f198])).

fof(f198,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(unit_resulting_resolution,[],[f183,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f163,f104])).

fof(f104,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f51])).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f163,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f156,f98])).

fof(f98,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f55,f51,f51])).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f156,plain,(
    ! [X0] : r1_tarski(k2_relat_1(o_0_0_xboole_0),X0) ),
    inference(backward_demodulation,[],[f126,f144])).

fof(f144,plain,(
    ! [X0] : o_0_0_xboole_0 = sK2(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f128,f127,f106])).

fof(f106,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != k1_relat_1(X0)
      | o_0_0_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f51,f51])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f127,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_relat_1(sK2(X0,o_0_0_xboole_0)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X1
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f83,f51])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_relat_1(sK2(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( v1_relat_1(X2)
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f128,plain,(
    ! [X0] : v1_relat_1(sK2(X0,o_0_0_xboole_0)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f81,f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK2(X0,o_0_0_xboole_0)),X0) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f85,f51])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f183,plain,(
    ! [X0] : ~ r1_tarski(k9_setfam_1(X0),X0) ),
    inference(unit_resulting_resolution,[],[f182,f124])).

fof(f124,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f77,f56])).

fof(f56,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f182,plain,(
    ! [X4] : ~ r2_hidden(X4,X4) ),
    inference(superposition,[],[f129,f179])).

fof(f179,plain,(
    ! [X0] : k6_subset_1(k5_xboole_0(X0,k6_subset_1(k2_enumset1(X0,X0,X0,X0),X0)),k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f102,f107])).

fof(f107,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f71,f92,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (17576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f102,plain,(
    ! [X0] : k6_subset_1(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f94,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f90])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f94,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f61,f92,f93])).

fof(f61,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f62,plain,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

fof(f129,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f88,f67,f93])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f267,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(subsumption_resolution,[],[f153,f174])).

fof(f174,plain,(
    ! [X0] : r2_hidden(o_0_0_xboole_0,k9_setfam_1(X0)) ),
    inference(unit_resulting_resolution,[],[f163,f124])).

fof(f153,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(o_0_0_xboole_0,k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f103,f101])).

fof(f101,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f59,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f103,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(o_0_0_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f51,f51])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f95,plain,(
    o_0_0_xboole_0 != k3_yellow_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(definition_unfolding,[],[f50,f51,f58])).

fof(f50,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f38])).

fof(f38,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (17561)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (17562)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (17585)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (17585)Refutation not found, incomplete strategy% (17585)------------------------------
% 0.21/0.50  % (17585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17585)Memory used [KB]: 6140
% 0.21/0.50  % (17585)Time elapsed: 0.107 s
% 0.21/0.50  % (17585)------------------------------
% 0.21/0.50  % (17585)------------------------------
% 0.21/0.51  % (17570)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (17578)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (17569)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (17563)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (17569)Refutation not found, incomplete strategy% (17569)------------------------------
% 0.21/0.52  % (17569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17569)Memory used [KB]: 10746
% 0.21/0.52  % (17569)Time elapsed: 0.118 s
% 0.21/0.52  % (17569)------------------------------
% 0.21/0.52  % (17569)------------------------------
% 0.21/0.52  % (17573)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (17586)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (17586)Refutation not found, incomplete strategy% (17586)------------------------------
% 0.21/0.52  % (17586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17586)Memory used [KB]: 6140
% 0.21/0.52  % (17586)Time elapsed: 0.115 s
% 0.21/0.52  % (17586)------------------------------
% 0.21/0.52  % (17586)------------------------------
% 0.21/0.53  % (17571)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (17564)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (17563)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (17582)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (17574)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (17581)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (17584)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (17587)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (17560)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (17560)Refutation not found, incomplete strategy% (17560)------------------------------
% 0.21/0.53  % (17560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17560)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17560)Memory used [KB]: 1663
% 0.21/0.53  % (17560)Time elapsed: 0.125 s
% 0.21/0.53  % (17560)------------------------------
% 0.21/0.53  % (17560)------------------------------
% 0.21/0.54  % (17571)Refutation not found, incomplete strategy% (17571)------------------------------
% 0.21/0.54  % (17571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17588)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (17565)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (17579)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (17573)Refutation not found, incomplete strategy% (17573)------------------------------
% 0.21/0.54  % (17573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17573)Memory used [KB]: 1663
% 0.21/0.54  % (17573)Time elapsed: 0.125 s
% 0.21/0.54  % (17573)------------------------------
% 0.21/0.54  % (17573)------------------------------
% 0.21/0.54  % (17580)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (17577)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (17575)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (17584)Refutation not found, incomplete strategy% (17584)------------------------------
% 0.21/0.54  % (17584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17575)Refutation not found, incomplete strategy% (17575)------------------------------
% 0.21/0.54  % (17575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17575)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17575)Memory used [KB]: 10618
% 0.21/0.54  % (17575)Time elapsed: 0.139 s
% 0.21/0.54  % (17575)------------------------------
% 0.21/0.54  % (17575)------------------------------
% 0.21/0.54  % (17568)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (17577)Refutation not found, incomplete strategy% (17577)------------------------------
% 0.21/0.54  % (17577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17577)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17577)Memory used [KB]: 1663
% 0.21/0.54  % (17577)Time elapsed: 0.139 s
% 0.21/0.54  % (17577)------------------------------
% 0.21/0.54  % (17577)------------------------------
% 0.21/0.54  % (17572)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (17584)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17584)Memory used [KB]: 6140
% 0.21/0.54  % (17584)Time elapsed: 0.138 s
% 0.21/0.54  % (17584)------------------------------
% 0.21/0.54  % (17584)------------------------------
% 0.21/0.54  % (17571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17571)Memory used [KB]: 10618
% 0.21/0.54  % (17571)Time elapsed: 0.134 s
% 0.21/0.54  % (17571)------------------------------
% 0.21/0.54  % (17571)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f276])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    o_0_0_xboole_0 != o_0_0_xboole_0),
% 0.21/0.54    inference(superposition,[],[f95,f268])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f198])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f183,f175])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(superposition,[],[f163,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f64,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f156,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f51,f51])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(o_0_0_xboole_0),X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f126,f144])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 = sK2(X0,o_0_0_xboole_0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f128,f127,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 != k1_relat_1(X0) | o_0_0_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f65,f51,f51])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 = k1_relat_1(sK2(X0,o_0_0_xboole_0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X1 | o_0_0_xboole_0 != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f83,f51])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_relat_1(sK2(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : (v1_relat_1(X2) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(sK2(X0,o_0_0_xboole_0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | o_0_0_xboole_0 != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f81,f51])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(sK2(X0,o_0_0_xboole_0)),X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) | o_0_0_xboole_0 != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f85,f51])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k9_setfam_1(X0),X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f182,f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f77,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,axiom,(
% 0.21/0.54    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X4] : (~r2_hidden(X4,X4)) )),
% 0.21/0.54    inference(superposition,[],[f129,f179])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(k5_xboole_0(X0,k6_subset_1(k2_enumset1(X0,X0,X0,X0),X0)),k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f102,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f71,f92,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f69,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f70,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  % (17576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f62,f94,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f60,f90])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f61,f92,f93])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,axiom,(
% 0.21/0.55    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.21/0.55    inference(equality_resolution,[],[f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f88,f67,f93])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.55    inference(flattening,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.55    inference(nnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.55  fof(f267,plain,(
% 0.21/0.55    ( ! [X0] : (o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f153,f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(o_0_0_xboole_0,k9_setfam_1(X0))) )),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f163,f124])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X0] : (o_0_0_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(o_0_0_xboole_0,k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.55    inference(superposition,[],[f103,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f59,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,axiom,(
% 0.21/0.55    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,axiom,(
% 0.21/0.55    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X0] : (o_0_0_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(o_0_0_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f63,f51,f51])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,axiom,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    o_0_0_xboole_0 != k3_yellow_0(k3_lattice3(k1_lattice3(sK0)))),
% 0.21/0.55    inference(definition_unfolding,[],[f50,f51,f58])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,negated_conjecture,(
% 0.21/0.55    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f27])).
% 0.21/0.55  fof(f27,conjecture,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (17563)------------------------------
% 0.21/0.55  % (17563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17563)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (17563)Memory used [KB]: 1791
% 0.21/0.55  % (17563)Time elapsed: 0.125 s
% 0.21/0.55  % (17563)------------------------------
% 0.21/0.55  % (17563)------------------------------
% 0.21/0.55  % (17576)Refutation not found, incomplete strategy% (17576)------------------------------
% 0.21/0.55  % (17576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17576)Memory used [KB]: 1791
% 0.21/0.55  % (17576)Time elapsed: 0.113 s
% 0.21/0.55  % (17576)------------------------------
% 0.21/0.55  % (17576)------------------------------
% 0.21/0.55  % (17588)Refutation not found, incomplete strategy% (17588)------------------------------
% 0.21/0.55  % (17588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17588)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17588)Memory used [KB]: 1663
% 0.21/0.55  % (17588)Time elapsed: 0.139 s
% 0.21/0.55  % (17588)------------------------------
% 0.21/0.55  % (17588)------------------------------
% 0.21/0.55  % (17587)Refutation not found, incomplete strategy% (17587)------------------------------
% 0.21/0.55  % (17587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17587)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17587)Memory used [KB]: 10746
% 0.21/0.55  % (17587)Time elapsed: 0.140 s
% 0.21/0.55  % (17558)Success in time 0.186 s
%------------------------------------------------------------------------------
