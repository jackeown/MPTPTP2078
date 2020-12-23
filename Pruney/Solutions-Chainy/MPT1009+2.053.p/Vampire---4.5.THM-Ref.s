%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 333 expanded)
%              Number of leaves         :   24 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  317 ( 875 expanded)
%              Number of equality atoms :   88 ( 247 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f165,f177,f209,f215,f279,f280,f363])).

fof(f363,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f361,f47])).

% (24328)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f361,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f360,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f132,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f132,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

% (24315)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f110,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_relat_1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f110,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k1_xboole_0,X1)
      | k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f109,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f109,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k1_xboole_0,X1)
      | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f104,f48])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v4_relat_1(X0,X1)
      | k2_relat_1(X0) = k9_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(superposition,[],[f54,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ v4_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f58,f62])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f360,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f102,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f101,f69])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f101,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f68,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f44,f67,f67])).

fof(f44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f280,plain,
    ( spl4_10
    | spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f232,f158,f185,f181])).

fof(f181,plain,
    ( spl4_10
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f185,plain,
    ( spl4_11
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f158,plain,
    ( spl4_8
  <=> r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f232,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(resolution,[],[f159,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f59,f67,f67])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f159,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f279,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f274,f153])).

fof(f153,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_7
  <=> ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f274,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f102,f272])).

fof(f272,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f271,f175])).

fof(f175,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f271,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(resolution,[],[f237,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k2_relat_1(X0) = k1_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0))
        | k1_relat_1(X0) != k1_relat_1(sK3)
        | ~ v1_relat_1(X0) )
    | ~ spl4_10 ),
    inference(superposition,[],[f71,f183])).

fof(f183,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f181])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_enumset1(X0,X0,X0)
      | k2_relat_1(X1) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f67,f67])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f215,plain,
    ( spl4_2
    | ~ spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f213,f174,f185,f96])).

% (24315)Refutation not found, incomplete strategy% (24315)------------------------------
% (24315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24315)Termination reason: Refutation not found, incomplete strategy

% (24315)Memory used [KB]: 10618
% (24315)Time elapsed: 0.106 s
% (24315)------------------------------
% (24315)------------------------------
fof(f213,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_9 ),
    inference(resolution,[],[f175,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f209,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f69,f204])).

fof(f204,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_9 ),
    inference(resolution,[],[f176,f62])).

fof(f176,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( ~ spl4_9
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f167,f148,f158,f174])).

fof(f148,plain,
    ( spl4_6
  <=> v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f167,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f149,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,
    ( v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f165,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f156,f69])).

fof(f156,plain,
    ( ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),X2)))
    | spl4_6 ),
    inference(resolution,[],[f150,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f150,plain,
    ( ~ v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f154,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f146,f152,f148])).

fof(f146,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
      | ~ v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) ) ),
    inference(superposition,[],[f141,f123])).

fof(f123,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) ),
    inference(resolution,[],[f112,f69])).

fof(f112,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_relat_1(sK3) = k9_relat_1(sK3,X3) ) ),
    inference(resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | k2_relat_1(sK3) = k9_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f104,f69])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0))
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f140,f69])).

fof(f140,plain,(
    ! [X6,X4,X0,X5,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v4_relat_1(X0,X1)
      | r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f139,f62])).

fof(f139,plain,(
    ! [X6,X4,X0,X5,X1] :
      ( r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(condensation,[],[f138])).

fof(f138,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(superposition,[],[f86,f83])).

fof(f86,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r1_tarski(k9_relat_1(k7_relat_1(X3,X4),X5),k9_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f77,f54])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X0,X3),k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

% (24309)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (24307)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (24322)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (24331)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (24313)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (24306)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24308)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24308)Refutation not found, incomplete strategy% (24308)------------------------------
% 0.21/0.51  % (24308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24308)Memory used [KB]: 6268
% 0.21/0.51  % (24308)Time elapsed: 0.098 s
% 0.21/0.51  % (24308)------------------------------
% 0.21/0.51  % (24308)------------------------------
% 0.21/0.51  % (24329)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (24305)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24307)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (24310)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (24320)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f154,f165,f177,f209,f215,f279,f280,f363])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f362])).
% 0.21/0.52  fof(f362,plain,(
% 0.21/0.52    $false | ~spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f361,f47])).
% 0.21/0.52  % (24328)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.52    inference(forward_demodulation,[],[f360,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f133,f47])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f132,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  % (24315)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(resolution,[],[f110,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v4_relat_1(X0,X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(resolution,[],[f56,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X1] : (~v4_relat_1(k1_xboole_0,X1) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f109,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X1] : (~v4_relat_1(k1_xboole_0,X1) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f104,f48])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v4_relat_1(X0,X1) | k2_relat_1(X0) = k9_relat_1(X0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f62])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(superposition,[],[f54,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X0,X1) = X0 | ~v4_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(resolution,[],[f58,f62])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f360,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.52    inference(forward_demodulation,[],[f102,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_2 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f49,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.21/0.52    inference(superposition,[],[f68,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.21/0.52    inference(definition_unfolding,[],[f44,f67,f67])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    spl4_10 | spl4_11 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f232,f158,f185,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl4_10 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl4_11 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl4_8 <=> r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK3) | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_8),
% 0.21/0.52    inference(resolution,[],[f159,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f59,f67,f67])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f158])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    ~spl4_7 | ~spl4_9 | ~spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    $false | (~spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl4_7 <=> ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_9 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f102,f272])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_9 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f271,f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    spl4_9 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_10),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f270])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_10),
% 0.21/0.52    inference(resolution,[],[f237,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k1_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(X0)) ) | ~spl4_10),
% 0.21/0.52    inference(superposition,[],[f71,f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f181])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X1) != k1_enumset1(X0,X0,X0) | k2_relat_1(X1) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f57,f67,f67])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    spl4_2 | ~spl4_11 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f213,f174,f185,f96])).
% 0.21/0.52  % (24315)Refutation not found, incomplete strategy% (24315)------------------------------
% 0.21/0.52  % (24315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24315)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24315)Memory used [KB]: 10618
% 0.21/0.52  % (24315)Time elapsed: 0.106 s
% 0.21/0.52  % (24315)------------------------------
% 0.21/0.52  % (24315)------------------------------
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK3 | ~spl4_9),
% 0.21/0.52    inference(resolution,[],[f175,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    spl4_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    $false | spl4_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f204])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_9),
% 0.21/0.52    inference(resolution,[],[f176,f62])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f174])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ~spl4_9 | spl4_8 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f148,f158,f174])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_6 <=> v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) | ~v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.52    inference(resolution,[],[f149,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl4_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    $false | spl4_6),
% 0.21/0.52    inference(resolution,[],[f156,f69])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),X2)))) ) | spl4_6),
% 0.21/0.52    inference(resolution,[],[f150,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) | spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~spl4_6 | spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f146,f152,f148])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0))) )),
% 0.21/0.52    inference(superposition,[],[f141,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k2_relat_1(sK3) = k9_relat_1(sK3,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    inference(resolution,[],[f112,f69])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X4,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_relat_1(sK3) = k9_relat_1(sK3,X3)) )),
% 0.21/0.52    inference(resolution,[],[f108,f63])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(sK3,X0) | k2_relat_1(sK3) = k9_relat_1(sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f104,f69])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK3,X1),k9_relat_1(sK3,X0)) | ~v4_relat_1(sK3,X0)) )),
% 0.21/0.52    inference(resolution,[],[f140,f69])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X6,X4,X0,X5,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v4_relat_1(X0,X1) | r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f139,f62])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X6,X4,X0,X5,X1] : (r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.21/0.52    inference(condensation,[],[f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_tarski(k9_relat_1(X0,X4),k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.21/0.52    inference(superposition,[],[f86,f83])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | r1_tarski(k9_relat_1(k7_relat_1(X3,X4),X5),k9_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 0.21/0.52    inference(superposition,[],[f77,f54])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X0,X3),k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(resolution,[],[f62,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.52  % (24309)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (24307)------------------------------
% 0.21/0.52  % (24307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24307)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24307)Memory used [KB]: 10874
% 0.21/0.52  % (24307)Time elapsed: 0.096 s
% 0.21/0.52  % (24307)------------------------------
% 0.21/0.52  % (24307)------------------------------
% 0.21/0.52  % (24316)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24319)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (24301)Success in time 0.165 s
%------------------------------------------------------------------------------
