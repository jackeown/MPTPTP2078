%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:26 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 336 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 ( 833 expanded)
%              Number of equality atoms :  100 ( 325 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f225,f250,f605,f635,f989])).

fof(f989,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f988])).

fof(f988,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f987,f103])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f82])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38])).

fof(f38,plain,
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

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f987,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f971,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f971,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f320,f725])).

fof(f725,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f724,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f724,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f723,f604])).

fof(f604,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl4_11
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f723,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f722,f103])).

fof(f722,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f715,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f715,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f681,f270])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0))
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(extensionality_resolution,[],[f64,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f80,f80])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f681,plain,
    ( ! [X4] : r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X4))
    | ~ spl4_11 ),
    inference(superposition,[],[f94,f604])).

fof(f94,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f74,f79,f80])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f320,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f81,f194])).

fof(f194,plain,(
    ! [X7] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X7) = k9_relat_1(sK3,X7) ),
    inference(resolution,[],[f77,f82])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

% (10021)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (10016)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (10021)Refutation not found, incomplete strategy% (10021)------------------------------
% (10021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10021)Termination reason: Refutation not found, incomplete strategy

% (10021)Memory used [KB]: 1663
% (10021)Time elapsed: 0.153 s
% (10021)------------------------------
% (10021)------------------------------
% (10016)Refutation not found, incomplete strategy% (10016)------------------------------
% (10016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10016)Termination reason: Refutation not found, incomplete strategy

% (10016)Memory used [KB]: 10618
% (10016)Time elapsed: 0.157 s
% (10016)------------------------------
% (10016)------------------------------
% (10010)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f81,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f50,f80,f80])).

fof(f50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f635,plain,
    ( ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f613,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f613,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f254,f600])).

fof(f600,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f254,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f224,f90])).

fof(f224,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(sK3),X4)
        | ~ v1_xboole_0(X4) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_5
  <=> ! [X4] :
        ( ~ r1_tarski(k1_relat_1(sK3),X4)
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f605,plain,
    ( spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f596,f602,f598])).

fof(f596,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f592,f103])).

fof(f592,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f282,f131])).

fof(f131,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f69,f82])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

% (10020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f282,plain,(
    ! [X10,X8,X9] :
      ( ~ v4_relat_1(X9,k2_enumset1(X10,X10,X10,X8))
      | k1_relat_1(X9) = k2_enumset1(X10,X10,X10,X10)
      | k1_xboole_0 = k1_relat_1(X9)
      | k1_relat_1(X9) = k2_enumset1(X10,X10,X10,X8)
      | k2_enumset1(X8,X8,X8,X8) = k1_relat_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f89,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f72,f79,f80,f80,f79])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f250,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f248,f97])).

fof(f97,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f248,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f238,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f192,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f192,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f77,f52])).

fof(f238,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f81,f236])).

fof(f236,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(resolution,[],[f145,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f145,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f225,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f215,f223,f143])).

fof(f215,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(sK3),X4)
      | v1_xboole_0(sK3)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f207,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f207,plain,(
    ! [X6] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,sK1)))
      | ~ r1_tarski(k1_relat_1(sK3),X6) ) ),
    inference(resolution,[],[f78,f82])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (9998)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (10006)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (10013)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (9996)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (10006)Refutation not found, incomplete strategy% (10006)------------------------------
% 0.21/0.53  % (10006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10006)Memory used [KB]: 1791
% 0.21/0.53  % (10006)Time elapsed: 0.123 s
% 0.21/0.53  % (10006)------------------------------
% 0.21/0.53  % (10006)------------------------------
% 0.21/0.53  % (9997)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (9995)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (9994)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (10009)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.54  % (10012)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.54  % (10011)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.55  % (10005)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.55  % (10001)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.55  % (10004)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.36/0.55  % (10003)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.55  % (9993)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.55  % (10017)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.36/0.55  % (9993)Refutation not found, incomplete strategy% (9993)------------------------------
% 1.36/0.55  % (9993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (9993)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (9993)Memory used [KB]: 1663
% 1.36/0.55  % (9993)Time elapsed: 0.140 s
% 1.36/0.55  % (9993)------------------------------
% 1.36/0.55  % (9993)------------------------------
% 1.36/0.55  % (10000)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.55  % (10002)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.55  % (9992)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.55  % (9998)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f990,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(avatar_sat_refutation,[],[f225,f250,f605,f635,f989])).
% 1.36/0.56  fof(f989,plain,(
% 1.36/0.56    ~spl4_11),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f988])).
% 1.36/0.56  fof(f988,plain,(
% 1.36/0.56    $false | ~spl4_11),
% 1.36/0.56    inference(subsumption_resolution,[],[f987,f103])).
% 1.36/0.56  fof(f103,plain,(
% 1.36/0.56    v1_relat_1(sK3)),
% 1.36/0.56    inference(resolution,[],[f68,f82])).
% 1.36/0.56  fof(f82,plain,(
% 1.36/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.36/0.56    inference(definition_unfolding,[],[f48,f80])).
% 1.36/0.56  fof(f80,plain,(
% 1.36/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f54,f79])).
% 1.36/0.56  fof(f79,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f56,f67])).
% 1.36/0.56  fof(f67,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.56  fof(f54,plain,(
% 1.36/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f4])).
% 1.36/0.56  fof(f4,axiom,(
% 1.36/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.36/0.56    inference(cnf_transformation,[],[f39])).
% 1.36/0.56  fof(f39,plain,(
% 1.36/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.36/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38])).
% 1.36/0.56  fof(f38,plain,(
% 1.36/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.36/0.56    inference(flattening,[],[f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.36/0.56    inference(ennf_transformation,[],[f21])).
% 1.36/0.56  fof(f21,negated_conjecture,(
% 1.36/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.56    inference(negated_conjecture,[],[f20])).
% 1.36/0.56  fof(f20,conjecture,(
% 1.36/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.36/0.56  fof(f68,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f30])).
% 1.36/0.56  fof(f30,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f15])).
% 1.36/0.56  fof(f15,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.56  fof(f987,plain,(
% 1.36/0.56    ~v1_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(resolution,[],[f971,f57])).
% 1.36/0.56  fof(f57,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f25])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f12])).
% 1.36/0.56  fof(f12,axiom,(
% 1.36/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.36/0.56  fof(f971,plain,(
% 1.36/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_11),
% 1.36/0.56    inference(backward_demodulation,[],[f320,f725])).
% 1.36/0.56  fof(f725,plain,(
% 1.36/0.56    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(subsumption_resolution,[],[f724,f90])).
% 1.36/0.56  fof(f90,plain,(
% 1.36/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.56    inference(equality_resolution,[],[f63])).
% 1.36/0.56  fof(f63,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f42])).
% 1.36/0.56  fof(f42,plain,(
% 1.36/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.56    inference(flattening,[],[f41])).
% 1.36/0.56  fof(f41,plain,(
% 1.36/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.56    inference(nnf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.56  fof(f724,plain,(
% 1.36/0.56    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(forward_demodulation,[],[f723,f604])).
% 1.36/0.56  fof(f604,plain,(
% 1.36/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(avatar_component_clause,[],[f602])).
% 1.36/0.56  fof(f602,plain,(
% 1.36/0.56    spl4_11 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.36/0.56  fof(f723,plain,(
% 1.36/0.56    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(subsumption_resolution,[],[f722,f103])).
% 1.36/0.56  fof(f722,plain,(
% 1.36/0.56    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(subsumption_resolution,[],[f715,f46])).
% 1.36/0.56  fof(f46,plain,(
% 1.36/0.56    v1_funct_1(sK3)),
% 1.36/0.56    inference(cnf_transformation,[],[f39])).
% 1.36/0.56  fof(f715,plain,(
% 1.36/0.56    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_11),
% 1.36/0.56    inference(resolution,[],[f681,f270])).
% 1.36/0.56  fof(f270,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0)) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1)) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.56    inference(extensionality_resolution,[],[f64,f84])).
% 1.36/0.56  fof(f84,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f61,f80,f80])).
% 1.36/0.56  fof(f61,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f29])).
% 1.36/0.56  fof(f29,plain,(
% 1.36/0.56    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.36/0.56    inference(flattening,[],[f28])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.36/0.56    inference(ennf_transformation,[],[f14])).
% 1.36/0.56  fof(f14,axiom,(
% 1.36/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.36/0.56  fof(f64,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f42])).
% 1.36/0.56  fof(f681,plain,(
% 1.36/0.56    ( ! [X4] : (r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X4))) ) | ~spl4_11),
% 1.36/0.56    inference(superposition,[],[f94,f604])).
% 1.36/0.56  fof(f94,plain,(
% 1.36/0.56    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) )),
% 1.36/0.56    inference(equality_resolution,[],[f87])).
% 1.36/0.56  fof(f87,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) != X0) )),
% 1.36/0.56    inference(definition_unfolding,[],[f74,f79,f80])).
% 1.36/0.56  fof(f74,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f45])).
% 1.36/0.56  fof(f45,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.36/0.56    inference(flattening,[],[f44])).
% 1.36/0.56  fof(f44,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.36/0.56    inference(nnf_transformation,[],[f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.36/0.56  fof(f320,plain,(
% 1.36/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.36/0.56    inference(backward_demodulation,[],[f81,f194])).
% 1.36/0.56  fof(f194,plain,(
% 1.36/0.56    ( ! [X7] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X7) = k9_relat_1(sK3,X7)) )),
% 1.36/0.56    inference(resolution,[],[f77,f82])).
% 1.36/0.56  fof(f77,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f35])).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,axiom,(
% 1.36/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.36/0.56  % (10021)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.56  % (10016)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.56  % (10021)Refutation not found, incomplete strategy% (10021)------------------------------
% 1.36/0.56  % (10021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (10021)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (10021)Memory used [KB]: 1663
% 1.36/0.56  % (10021)Time elapsed: 0.153 s
% 1.36/0.56  % (10021)------------------------------
% 1.36/0.56  % (10021)------------------------------
% 1.36/0.56  % (10016)Refutation not found, incomplete strategy% (10016)------------------------------
% 1.36/0.56  % (10016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (10016)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (10016)Memory used [KB]: 10618
% 1.36/0.56  % (10016)Time elapsed: 0.157 s
% 1.36/0.56  % (10016)------------------------------
% 1.36/0.56  % (10016)------------------------------
% 1.51/0.56  % (10010)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.51/0.56    inference(definition_unfolding,[],[f50,f80,f80])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f39])).
% 1.51/0.56  fof(f635,plain,(
% 1.51/0.56    ~spl4_5 | ~spl4_10),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f634])).
% 1.51/0.56  fof(f634,plain,(
% 1.51/0.56    $false | (~spl4_5 | ~spl4_10)),
% 1.51/0.56    inference(subsumption_resolution,[],[f613,f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    inference(cnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.56  fof(f613,plain,(
% 1.51/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_10)),
% 1.51/0.56    inference(backward_demodulation,[],[f254,f600])).
% 1.51/0.56  fof(f600,plain,(
% 1.51/0.56    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_10),
% 1.51/0.56    inference(avatar_component_clause,[],[f598])).
% 1.51/0.56  fof(f598,plain,(
% 1.51/0.56    spl4_10 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.51/0.56  fof(f254,plain,(
% 1.51/0.56    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl4_5),
% 1.51/0.56    inference(resolution,[],[f224,f90])).
% 1.51/0.56  fof(f224,plain,(
% 1.51/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(sK3),X4) | ~v1_xboole_0(X4)) ) | ~spl4_5),
% 1.51/0.56    inference(avatar_component_clause,[],[f223])).
% 1.51/0.56  fof(f223,plain,(
% 1.51/0.56    spl4_5 <=> ! [X4] : (~r1_tarski(k1_relat_1(sK3),X4) | ~v1_xboole_0(X4))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.51/0.56  fof(f605,plain,(
% 1.51/0.56    spl4_10 | spl4_11),
% 1.51/0.56    inference(avatar_split_clause,[],[f596,f602,f598])).
% 1.51/0.56  fof(f596,plain,(
% 1.51/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f592,f103])).
% 1.51/0.56  fof(f592,plain,(
% 1.51/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f591])).
% 1.51/0.56  fof(f591,plain,(
% 1.51/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.51/0.56    inference(resolution,[],[f282,f131])).
% 1.51/0.56  fof(f131,plain,(
% 1.51/0.56    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.51/0.56    inference(resolution,[],[f69,f82])).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f16])).
% 1.51/0.56  fof(f16,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.51/0.56  % (10020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.56  fof(f282,plain,(
% 1.51/0.56    ( ! [X10,X8,X9] : (~v4_relat_1(X9,k2_enumset1(X10,X10,X10,X8)) | k1_relat_1(X9) = k2_enumset1(X10,X10,X10,X10) | k1_xboole_0 = k1_relat_1(X9) | k1_relat_1(X9) = k2_enumset1(X10,X10,X10,X8) | k2_enumset1(X8,X8,X8,X8) = k1_relat_1(X9) | ~v1_relat_1(X9)) )),
% 1.51/0.56    inference(resolution,[],[f89,f58])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X2) = X0) )),
% 1.51/0.56    inference(definition_unfolding,[],[f72,f79,f80,f80,f79])).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f45])).
% 1.51/0.56  fof(f250,plain,(
% 1.51/0.56    ~spl4_4),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f249])).
% 1.51/0.56  fof(f249,plain,(
% 1.51/0.56    $false | ~spl4_4),
% 1.51/0.56    inference(subsumption_resolution,[],[f248,f97])).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.56    inference(resolution,[],[f65,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.56    inference(nnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.56  fof(f248,plain,(
% 1.51/0.56    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_4),
% 1.51/0.56    inference(forward_demodulation,[],[f238,f196])).
% 1.51/0.56  fof(f196,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 1.51/0.56    inference(forward_demodulation,[],[f192,f53])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.51/0.56  fof(f192,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 1.51/0.56    inference(resolution,[],[f77,f52])).
% 1.51/0.56  fof(f238,plain,(
% 1.51/0.56    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_4),
% 1.51/0.56    inference(backward_demodulation,[],[f81,f236])).
% 1.51/0.56  fof(f236,plain,(
% 1.51/0.56    k1_xboole_0 = sK3 | ~spl4_4),
% 1.51/0.56    inference(resolution,[],[f145,f55])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.51/0.56  fof(f145,plain,(
% 1.51/0.56    v1_xboole_0(sK3) | ~spl4_4),
% 1.51/0.56    inference(avatar_component_clause,[],[f143])).
% 1.51/0.56  fof(f143,plain,(
% 1.51/0.56    spl4_4 <=> v1_xboole_0(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.51/0.56  fof(f225,plain,(
% 1.51/0.56    spl4_4 | spl4_5),
% 1.51/0.56    inference(avatar_split_clause,[],[f215,f223,f143])).
% 1.51/0.56  fof(f215,plain,(
% 1.51/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(sK3),X4) | v1_xboole_0(sK3) | ~v1_xboole_0(X4)) )),
% 1.51/0.56    inference(resolution,[],[f207,f60])).
% 1.51/0.56  fof(f60,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,axiom,(
% 1.51/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.51/0.56  fof(f207,plain,(
% 1.51/0.56    ( ! [X6] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,sK1))) | ~r1_tarski(k1_relat_1(sK3),X6)) )),
% 1.51/0.56    inference(resolution,[],[f78,f82])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.51/0.56    inference(flattening,[],[f36])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.51/0.56    inference(ennf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (9998)------------------------------
% 1.51/0.56  % (9998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (9998)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (9998)Memory used [KB]: 11129
% 1.51/0.56  % (9998)Time elapsed: 0.133 s
% 1.51/0.56  % (9998)------------------------------
% 1.51/0.56  % (9998)------------------------------
% 1.51/0.56  % (10010)Refutation not found, incomplete strategy% (10010)------------------------------
% 1.51/0.56  % (10010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (10010)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (10010)Memory used [KB]: 1791
% 1.51/0.56  % (10010)Time elapsed: 0.158 s
% 1.51/0.56  % (10010)------------------------------
% 1.51/0.56  % (10010)------------------------------
% 1.51/0.56  % (10019)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.56  % (10009)Refutation not found, incomplete strategy% (10009)------------------------------
% 1.51/0.56  % (10009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (10009)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (10009)Memory used [KB]: 1791
% 1.51/0.56  % (10009)Time elapsed: 0.155 s
% 1.51/0.56  % (10009)------------------------------
% 1.51/0.56  % (10009)------------------------------
% 1.51/0.56  % (9991)Success in time 0.201 s
%------------------------------------------------------------------------------
