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
% DateTime   : Thu Dec  3 12:56:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 637 expanded)
%              Number of leaves         :   21 ( 177 expanded)
%              Depth                    :   21
%              Number of atoms          :  241 (1545 expanded)
%              Number of equality atoms :   75 ( 450 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1855,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f1720,f1854])).

fof(f1854,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f1853])).

fof(f1853,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f1852,f40])).

fof(f40,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f1852,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | spl3_1 ),
    inference(resolution,[],[f105,f1116])).

fof(f1116,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relset_1(sK0,sK1,sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2) ) ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f105,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_1
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1720,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1719])).

fof(f1719,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f1718,f1085])).

fof(f1085,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f109,f825])).

fof(f825,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f61,f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f109,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1718,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f1675,f115])).

fof(f115,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f111,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f111,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f91,f99])).

fof(f99,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f97,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f91,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1675,plain,(
    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f714,f1668])).

fof(f1668,plain,(
    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f692,f1666])).

fof(f1666,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f1659,f129])).

fof(f129,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) ) ),
    inference(subsumption_resolution,[],[f127,f42])).

fof(f127,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f123,f59])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_relat_1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f58,f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f1659,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f1658,f40])).

fof(f1658,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_relat_1(X0),sK2)
      | r1_tarski(X0,k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f1657,f825])).

fof(f1657,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_relat_1(X0),sK2)
      | r1_tarski(X0,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f692,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(superposition,[],[f689,f258])).

fof(f258,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f184,f183])).

fof(f183,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f180,f182])).

fof(f182,plain,(
    ! [X6,X7] : k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k9_relat_1(k6_relat_1(X6),X7) ),
    inference(backward_demodulation,[],[f165,f181])).

fof(f181,plain,(
    ! [X8,X9] : k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k9_relat_1(k6_relat_1(X8),X9) ),
    inference(forward_demodulation,[],[f166,f91])).

fof(f166,plain,(
    ! [X8,X9] : k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k2_relat_1(k7_relat_1(k6_relat_1(X8),X9)) ),
    inference(superposition,[],[f46,f90])).

fof(f90,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f69,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f69,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f165,plain,(
    ! [X6,X7] : k1_setfam_1(k2_enumset1(X6,X6,X6,X7)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(superposition,[],[f45,f90])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f180,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f90,f165])).

fof(f184,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f179,f182])).

fof(f179,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(backward_demodulation,[],[f160,f165])).

fof(f160,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[],[f90,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f66,f66])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f689,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f666,f86])).

fof(f86,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f666,plain,(
    ! [X1] :
      ( ~ v5_relat_1(sK2,X1)
      | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X1) ) ),
    inference(resolution,[],[f664,f129])).

fof(f664,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK2),X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(forward_demodulation,[],[f663,f101])).

fof(f101,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[],[f93,f100])).

fof(f100,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f98,f71])).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f98,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f85])).

fof(f85,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f62,f39])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X5] : k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5) ),
    inference(resolution,[],[f55,f71])).

fof(f663,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k9_relat_1(sK2,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f657,f71])).

fof(f657,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k9_relat_1(sK2,sK0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f96,f100])).

fof(f96,plain,(
    ! [X4,X3] :
      ( ~ v5_relat_1(k7_relat_1(sK2,X3),X4)
      | r1_tarski(k9_relat_1(sK2,X3),X4)
      | ~ v1_relat_1(k7_relat_1(sK2,X3)) ) ),
    inference(superposition,[],[f56,f93])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f714,plain,(
    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(forward_demodulation,[],[f694,f46])).

fof(f694,plain,(
    k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f91,f689])).

fof(f110,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f107,f103])).

fof(f41,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17063)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (17055)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (17058)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (17062)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (17056)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (17065)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17054)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (17061)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (17063)Refutation not found, incomplete strategy% (17063)------------------------------
% 0.21/0.49  % (17063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17063)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (17063)Memory used [KB]: 10618
% 0.21/0.49  % (17063)Time elapsed: 0.072 s
% 0.21/0.49  % (17063)------------------------------
% 0.21/0.49  % (17063)------------------------------
% 0.21/0.50  % (17066)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (17064)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (17059)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (17068)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (17052)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (17057)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (17067)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (17053)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (17069)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (17060)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.54  % (17061)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1855,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f110,f1720,f1854])).
% 0.21/0.54  fof(f1854,plain,(
% 0.21/0.54    spl3_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1853])).
% 0.21/0.54  fof(f1853,plain,(
% 0.21/0.54    $false | spl3_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f1852,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.21/0.54  fof(f1852,plain,(
% 0.21/0.54    ~r1_tarski(k6_relat_1(sK1),sK2) | spl3_1),
% 0.21/0.54    inference(resolution,[],[f105,f1116])).
% 0.21/0.54  fof(f1116,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k1_relset_1(sK0,sK1,sK2)) | ~r1_tarski(k6_relat_1(X0),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f64,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k1_relset_1(X0,X1,X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl3_1 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f1720,plain,(
% 0.21/0.54    spl3_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1719])).
% 0.21/0.54  fof(f1719,plain,(
% 0.21/0.54    $false | spl3_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f1718,f1085])).
% 0.21/0.54  fof(f1085,plain,(
% 0.21/0.54    sK1 != k2_relat_1(sK2) | spl3_2),
% 0.21/0.54    inference(superposition,[],[f109,f825])).
% 0.21/0.54  fof(f825,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f61,f39])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl3_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f1718,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f1675,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f111,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.54    inference(superposition,[],[f91,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f97,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(resolution,[],[f59,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f55,f42])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f1675,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(sK1),sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f714,f1668])).
% 0.21/0.54  fof(f1668,plain,(
% 0.21/0.54    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.21/0.54    inference(backward_demodulation,[],[f692,f1666])).
% 0.21/0.54  fof(f1666,plain,(
% 0.21/0.54    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.21/0.54    inference(resolution,[],[f1659,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f127,f42])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.54    inference(resolution,[],[f123,f59])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v4_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f121,f42])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v4_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f58,f43])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.54  fof(f1659,plain,(
% 0.21/0.54    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.54    inference(resolution,[],[f1658,f40])).
% 0.21/0.54  fof(f1658,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k6_relat_1(X0),sK2) | r1_tarski(X0,k2_relat_1(sK2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1657,f825])).
% 0.21/0.54  fof(f1657,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k6_relat_1(X0),sK2) | r1_tarski(X0,k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f65,f39])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k2_relset_1(X0,X1,X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f692,plain,(
% 0.21/0.54    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.21/0.54    inference(superposition,[],[f689,f258])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 0.21/0.54    inference(superposition,[],[f184,f183])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X0),X1))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f180,f182])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X6,X7] : (k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k9_relat_1(k6_relat_1(X6),X7)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f165,f181])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X8,X9] : (k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k9_relat_1(k6_relat_1(X8),X9)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f166,f91])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X8,X9] : (k1_setfam_1(k2_enumset1(X8,X8,X8,X9)) = k2_relat_1(k7_relat_1(k6_relat_1(X8),X9))) )),
% 0.21/0.54    inference(superposition,[],[f46,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f69,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f54,f42])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f53,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f52,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X6,X7] : (k1_setfam_1(k2_enumset1(X6,X6,X6,X7)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) )),
% 0.21/0.54    inference(superposition,[],[f45,f90])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f90,f165])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f179,f182])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f160,f165])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.54    inference(superposition,[],[f90,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f50,f66,f66])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f689,plain,(
% 0.21/0.54    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.21/0.54    inference(resolution,[],[f666,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    v5_relat_1(sK2,sK1)),
% 0.21/0.54    inference(resolution,[],[f63,f39])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f666,plain,(
% 0.21/0.54    ( ! [X1] : (~v5_relat_1(sK2,X1) | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X1)) )),
% 0.21/0.54    inference(resolution,[],[f664,f129])).
% 0.21/0.54  fof(f664,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),X0) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f663,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    k9_relat_1(sK2,sK0) = k2_relat_1(sK2)),
% 0.21/0.54    inference(superposition,[],[f93,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f70,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f48,f39])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.55    inference(resolution,[],[f59,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    v4_relat_1(sK2,sK0)),
% 0.21/0.55    inference(resolution,[],[f62,f39])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X5] : (k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5)) )),
% 0.21/0.55    inference(resolution,[],[f55,f71])).
% 0.21/0.55  fof(f663,plain,(
% 0.21/0.55    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k9_relat_1(sK2,sK0),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f657,f71])).
% 0.21/0.55  fof(f657,plain,(
% 0.21/0.55    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k9_relat_1(sK2,sK0),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.55    inference(superposition,[],[f96,f100])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X4,X3] : (~v5_relat_1(k7_relat_1(sK2,X3),X4) | r1_tarski(k9_relat_1(sK2,X3),X4) | ~v1_relat_1(k7_relat_1(sK2,X3))) )),
% 0.21/0.55    inference(superposition,[],[f56,f93])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.55  fof(f714,plain,(
% 0.21/0.55    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f694,f46])).
% 0.21/0.55  fof(f694,plain,(
% 0.21/0.55    k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.21/0.55    inference(superposition,[],[f91,f689])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ~spl3_1 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f41,f107,f103])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (17061)------------------------------
% 0.21/0.55  % (17061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17061)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (17061)Memory used [KB]: 11769
% 0.21/0.55  % (17061)Time elapsed: 0.117 s
% 0.21/0.55  % (17061)------------------------------
% 0.21/0.55  % (17061)------------------------------
% 0.21/0.55  % (17051)Success in time 0.188 s
%------------------------------------------------------------------------------
