%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  176 (1394 expanded)
%              Number of leaves         :   22 ( 347 expanded)
%              Depth                    :   31
%              Number of atoms          :  512 (7818 expanded)
%              Number of equality atoms :  106 (1863 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f553,f65])).

fof(f65,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
      | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
    & r1_tarski(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
        | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
      & r1_tarski(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f553,plain,(
    ~ r1_tarski(sK3,sK2) ),
    inference(forward_demodulation,[],[f552,f181])).

fof(f181,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f180,f137])).

fof(f137,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f69])).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f128,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f180,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f179,f127])).

fof(f127,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f64,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f179,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f170,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f170,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(resolution,[],[f136,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f136,plain,(
    sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f135,f61])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f135,plain,
    ( sP1(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f125,f63])).

fof(f63,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f125,plain,
    ( sP1(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f64,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f45,f50])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f552,plain,(
    ~ r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f551,f137])).

fof(f551,plain,
    ( ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f550,f61])).

fof(f550,plain,
    ( ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f549])).

fof(f549,plain,
    ( sK3 != sK3
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f540,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f540,plain,(
    sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f533,f65])).

fof(f533,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) ),
    inference(backward_demodulation,[],[f425,f516])).

fof(f516,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(resolution,[],[f510,f183])).

fof(f183,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK4))
    | sK2 = k1_relat_1(sK4) ),
    inference(resolution,[],[f161,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f161,plain,(
    r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f159,f137])).

fof(f159,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f126,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f126,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f64,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f510,plain,(
    r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f507,f373])).

fof(f373,plain,(
    sK2 = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(forward_demodulation,[],[f372,f330])).

fof(f330,plain,(
    sK2 = k2_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f329,f291])).

fof(f291,plain,(
    v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f282,f69])).

fof(f282,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f229,f68])).

fof(f229,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f226,f131])).

fof(f131,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f130,f61])).

fof(f130,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f129,f62])).

fof(f62,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f121,f63])).

fof(f121,plain,
    ( sP0(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f64,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f42,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f226,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f84,f134])).

fof(f134,plain,(
    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f133,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f132,f62])).

fof(f132,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f122,f63])).

fof(f122,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f64,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f329,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f328,f281])).

fof(f281,plain,(
    v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f229,f90])).

fof(f328,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v5_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f320,f77])).

fof(f320,plain,(
    v2_funct_2(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f290,f93])).

fof(f290,plain,(
    sP1(sK2,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f289,f196])).

fof(f196,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f195,f61])).

fof(f195,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f194,f62])).

fof(f194,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f193,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f192,f64])).

fof(f192,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f164,f80])).

fof(f164,plain,(
    v1_funct_1(k2_funct_2(sK2,sK4)) ),
    inference(resolution,[],[f131,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f289,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f279,f228])).

fof(f228,plain,(
    v3_funct_2(k2_funct_1(sK4),sK2,sK2) ),
    inference(subsumption_resolution,[],[f225,f131])).

fof(f225,plain,
    ( v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f83,f134])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f279,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f229,f94])).

fof(f372,plain,(
    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f371,f291])).

fof(f371,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f70,f310])).

fof(f310,plain,(
    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f308,f291])).

fof(f308,plain,
    ( k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f280,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f280,plain,(
    v4_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f229,f89])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f507,plain,(
    r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k1_relat_1(sK4)) ),
    inference(superposition,[],[f468,f250])).

fof(f250,plain,(
    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f249,f99])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f249,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f248,f181])).

fof(f248,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f247,f137])).

fof(f247,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f245,f61])).

fof(f245,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f75,f214])).

fof(f214,plain,(
    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f209,f137])).

fof(f209,plain,
    ( k1_relat_1(sK4) = k10_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f67,f181])).

fof(f67,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f468,plain,(
    ! [X2] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) ),
    inference(subsumption_resolution,[],[f467,f291])).

fof(f467,plain,(
    ! [X2] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)
      | ~ v1_relat_1(k2_funct_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f453,f196])).

fof(f453,plain,(
    ! [X2] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)
      | ~ v1_funct_1(k2_funct_1(sK4))
      | ~ v1_relat_1(k2_funct_1(sK4)) ) ),
    inference(superposition,[],[f73,f178])).

fof(f178,plain,(
    ! [X1] : k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) ),
    inference(subsumption_resolution,[],[f177,f137])).

fof(f177,plain,(
    ! [X1] :
      ( k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f174,f61])).

fof(f174,plain,(
    ! [X1] :
      ( k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f169,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f169,plain,(
    v2_funct_1(sK4) ),
    inference(resolution,[],[f136,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f425,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK4))
    | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f424,f123])).

fof(f123,plain,(
    ! [X0] : k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f64,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f424,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f423,f137])).

fof(f423,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f422,f61])).

fof(f422,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f416,f169])).

fof(f416,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f415])).

fof(f415,plain,
    ( sK3 != sK3
    | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f379,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f379,plain,
    ( sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f378,f124])).

fof(f124,plain,(
    ! [X1] : k8_relset_1(sK2,sK2,sK4,X1) = k10_relat_1(sK4,X1) ),
    inference(resolution,[],[f64,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f378,plain,
    ( sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f327,f124])).

fof(f327,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f66,f123])).

fof(f66,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:05:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (9371)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (9374)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (9370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (9372)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (9375)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (9378)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (9380)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (9377)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (9387)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (9367)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9374)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f554,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f553,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    r1_tarski(sK3,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    (sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f19])).
% 0.22/0.53  fof(f19,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 0.22/0.53  fof(f553,plain,(
% 0.22/0.53    ~r1_tarski(sK3,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f552,f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    sK2 = k2_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f137])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f128,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.22/0.53    inference(resolution,[],[f64,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f179,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    v5_relat_1(sK4,sK2)),
% 0.22/0.53    inference(resolution,[],[f64,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    sK2 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f170,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    v2_funct_2(sK4,sK2)),
% 0.22/0.53    inference(resolution,[],[f136,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | ~sP1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 0.22/0.53    inference(rectify,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    sP1(sK2,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f135,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    sP1(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f125,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    v3_funct_2(sK4,sK2,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    sP1(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f64,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(definition_folding,[],[f45,f50])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.53  fof(f552,plain,(
% 0.22/0.53    ~r1_tarski(sK3,k2_relat_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f551,f137])).
% 0.22/0.53  fof(f551,plain,(
% 0.22/0.53    ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f550,f61])).
% 0.22/0.53  fof(f550,plain,(
% 0.22/0.53    ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f549])).
% 0.22/0.53  fof(f549,plain,(
% 0.22/0.53    sK3 != sK3 | ~r1_tarski(sK3,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f540,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.53  fof(f540,plain,(
% 0.22/0.53    sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f533,f65])).
% 0.22/0.53  fof(f533,plain,(
% 0.22/0.53    ~r1_tarski(sK3,sK2) | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f425,f516])).
% 0.22/0.53  fof(f516,plain,(
% 0.22/0.53    sK2 = k1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f510,f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    ~r1_tarski(sK2,k1_relat_1(sK4)) | sK2 = k1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f161,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK4),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f159,f137])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f126,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    v4_relat_1(sK4,sK2)),
% 0.22/0.53    inference(resolution,[],[f64,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f510,plain,(
% 0.22/0.53    r1_tarski(sK2,k1_relat_1(sK4))),
% 0.22/0.53    inference(forward_demodulation,[],[f507,f373])).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    sK2 = k9_relat_1(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f372,f330])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    sK2 = k2_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f329,f291])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    v1_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f282,f69])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.22/0.53    inference(resolution,[],[f229,f68])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f226,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    sP0(sK2,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f130,f61])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    sP0(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f129,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    v1_funct_2(sK4,sK2,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    sP0(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f121,f63])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    sP0(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f64,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.53    inference(definition_folding,[],[f42,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.53    inference(flattening,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~sP0(sK2,sK4)),
% 0.22/0.53    inference(superposition,[],[f84,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f61])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f132,f62])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f122,f63])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f64,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f48])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f281])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    v5_relat_1(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(resolution,[],[f229,f90])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v5_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(resolution,[],[f320,f77])).
% 0.22/0.53  fof(f320,plain,(
% 0.22/0.53    v2_funct_2(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(resolution,[],[f290,f93])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    sP1(sK2,k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f289,f196])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f195,f61])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f62])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f63])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK4)) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f192,f64])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f164,f80])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_2(sK2,sK4))),
% 0.22/0.53    inference(resolution,[],[f131,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    sP1(sK2,k2_funct_1(sK4)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f279,f228])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    v3_funct_2(k2_funct_1(sK4),sK2,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f225,f131])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~sP0(sK2,sK4)),
% 0.22/0.53    inference(superposition,[],[f83,f134])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    sP1(sK2,k2_funct_1(sK4)) | ~v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(resolution,[],[f229,f94])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f371,f291])).
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    k2_relat_1(k2_funct_1(sK4)) = k9_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(superposition,[],[f70,f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f308,f291])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    k2_funct_1(sK4) = k7_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 0.22/0.53    inference(resolution,[],[f280,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    v4_relat_1(k2_funct_1(sK4),sK2)),
% 0.22/0.53    inference(resolution,[],[f229,f89])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  fof(f507,plain,(
% 0.22/0.53    r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k1_relat_1(sK4))),
% 0.22/0.53    inference(superposition,[],[f468,f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f249,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~r1_tarski(sK2,sK2) | sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 0.22/0.53    inference(forward_demodulation,[],[f248,f181])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f137])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f245,f61])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f75,f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    k1_relat_1(sK4) = k10_relat_1(sK4,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f209,f137])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f67,f181])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.53  fof(f468,plain,(
% 0.22/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f467,f291])).
% 0.22/0.53  fof(f467,plain,(
% 0.22/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) | ~v1_relat_1(k2_funct_1(sK4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f453,f196])).
% 0.22/0.53  fof(f453,plain,(
% 0.22/0.53    ( ! [X2] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X2)),X2) | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) )),
% 0.22/0.53    inference(superposition,[],[f73,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f177,f137])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) | ~v1_relat_1(sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f174,f61])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X1] : (k9_relat_1(sK4,X1) = k10_relat_1(k2_funct_1(sK4),X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 0.22/0.53    inference(resolution,[],[f169,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    v2_funct_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f136,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_funct_1(X1) | ~sP1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f60])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    ~r1_tarski(sK3,k1_relat_1(sK4)) | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))),
% 0.22/0.53    inference(forward_demodulation,[],[f424,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X0] : (k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 0.22/0.53    inference(resolution,[],[f64,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.53  fof(f424,plain,(
% 0.22/0.53    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f423,f137])).
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f422,f61])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f416,f169])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f415])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    sK3 != sK3 | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f379,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))),
% 0.22/0.53    inference(forward_demodulation,[],[f378,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X1] : (k8_relset_1(sK2,sK2,sK4,X1) = k10_relat_1(sK4,X1)) )),
% 0.22/0.53    inference(resolution,[],[f64,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f327,f124])).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f66,f123])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (9374)------------------------------
% 0.22/0.53  % (9374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9374)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (9374)Memory used [KB]: 1791
% 0.22/0.53  % (9374)Time elapsed: 0.104 s
% 0.22/0.53  % (9374)------------------------------
% 0.22/0.53  % (9374)------------------------------
% 0.22/0.53  % (9365)Success in time 0.166 s
%------------------------------------------------------------------------------
