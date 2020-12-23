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
% DateTime   : Thu Dec  3 13:06:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 685 expanded)
%              Number of leaves         :   20 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  351 (3735 expanded)
%              Number of equality atoms :   91 ( 980 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f160,f186,f234,f322])).

fof(f322,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f320,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

% (18486)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f320,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f319,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f75,f276,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f276,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f53,f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f319,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f190,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f190,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f100,f49,f126,f189,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f189,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(superposition,[],[f187,f149])).

fof(f149,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f52,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f187,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f93,f128])).

fof(f128,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_2
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f126,plain,(
    v2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f49,f51,f52,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f51,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f52,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f234,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f224,f96])).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f224,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2
    | spl3_4 ),
    inference(backward_demodulation,[],[f193,f211])).

fof(f211,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl3_4 ),
    inference(forward_demodulation,[],[f209,f197])).

fof(f197,plain,
    ( sK0 = k10_relat_1(sK2,sK0)
    | spl3_4 ),
    inference(superposition,[],[f161,f149])).

fof(f161,plain,
    ( sK0 = k8_relset_1(sK0,sK0,sK2,sK0)
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f50,f52,f159,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f159,plain,
    ( k1_xboole_0 != sK0
    | spl3_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f209,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | spl3_4 ),
    inference(superposition,[],[f178,f176])).

fof(f176,plain,
    ( k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0)
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f159,f138,f137,f64])).

fof(f137,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(backward_demodulation,[],[f120,f132])).

fof(f132,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f100,f110,f131,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f131,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f49,f51,f52,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f110,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f120,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f100,f49,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f138,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK0) ),
    inference(backward_demodulation,[],[f118,f132])).

fof(f118,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f100,f49,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f137,f77])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f190,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f186,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f184,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f183,f132])).

fof(f183,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f100,f49,f167,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f167,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(superposition,[],[f166,f128])).

fof(f166,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f89,f149])).

fof(f89,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_1
  <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f160,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f147,f157,f153])).

fof(f147,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f142,f100])).

fof(f142,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f74,f132])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f91,f87])).

fof(f54,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (18499)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (18489)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (18498)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18490)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18492)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (18485)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (18496)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (18508)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (18510)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (18487)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (18501)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (18505)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (18491)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (18506)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (18493)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (18485)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f94,f160,f186,f234,f322])).
% 0.21/0.51  fof(f322,plain,(
% 0.21/0.51    spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f321])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    $false | (spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f320,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  % (18486)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f319,f281])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f75,f276,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    r1_tarski(sK1,k1_xboole_0) | ~spl3_4),
% 0.21/0.51    inference(backward_demodulation,[],[f53,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl3_4 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f19])).
% 0.21/0.51  fof(f19,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k1_relat_1(k1_xboole_0)) | (spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f190,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl3_3 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl3_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f49,f126,f189,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 0.21/0.51    inference(superposition,[],[f187,f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f52,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 0.21/0.51    inference(forward_demodulation,[],[f93,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f52,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl3_2 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f49,f51,f52,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v3_funct_2(sK2,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f52,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    spl3_2 | spl3_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    $false | (spl3_2 | spl3_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f224,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f53,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_2 | spl3_4)),
% 0.21/0.51    inference(backward_demodulation,[],[f193,f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | spl3_4),
% 0.21/0.51    inference(forward_demodulation,[],[f209,f197])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    sK0 = k10_relat_1(sK2,sK0) | spl3_4),
% 0.21/0.51    inference(superposition,[],[f161,f149])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    sK0 = k8_relset_1(sK0,sK0,sK2,sK0) | spl3_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f49,f50,f52,f159,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | spl3_4),
% 0.21/0.51    inference(superposition,[],[f178,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0) | spl3_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f49,f159,f138,f137,f64])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f120,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    sK0 = k2_relat_1(sK2)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f110,f131,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    v2_funct_2(sK2,sK0)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f49,f51,f52,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    v5_relat_1(sK2,sK0)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f52,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f49,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f118,f132])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f49,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f137,f77])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_relat_1(sK2))) | spl3_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f190,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f185])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    $false | spl3_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f53])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK0) | spl3_1),
% 0.21/0.51    inference(forward_demodulation,[],[f183,f132])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl3_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f49,f167,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f166,f128])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | spl3_1),
% 0.21/0.51    inference(backward_demodulation,[],[f89,f149])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl3_1 <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f147,f157,f153])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f100])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f74,f132])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f91,f87])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18485)------------------------------
% 0.21/0.51  % (18485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18485)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18485)Memory used [KB]: 10874
% 0.21/0.51  % (18485)Time elapsed: 0.102 s
% 0.21/0.51  % (18485)------------------------------
% 0.21/0.51  % (18485)------------------------------
% 0.21/0.51  % (18481)Success in time 0.157 s
%------------------------------------------------------------------------------
