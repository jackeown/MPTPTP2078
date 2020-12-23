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
% DateTime   : Thu Dec  3 13:04:58 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 223 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   20
%              Number of atoms          :  406 ( 785 expanded)
%              Number of equality atoms :  153 ( 277 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f351,f364,f407])).

fof(f407,plain,(
    ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f394,f118])).

% (17347)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f118,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f72,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f394,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl9_26 ),
    inference(superposition,[],[f121,f350])).

fof(f350,plain,
    ( k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl9_26
  <=> k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

% (17348)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f121,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f112,f111])).

fof(f111,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f112,plain,(
    ! [X0,X1] : sP1(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f91,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f364,plain,(
    ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f359,f59])).

fof(f59,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(sK5,sK4)
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f359,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ spl9_25 ),
    inference(backward_demodulation,[],[f210,f352])).

fof(f352,plain,
    ( sK2 = k1_relat_1(sK5)
    | ~ spl9_25 ),
    inference(backward_demodulation,[],[f157,f346])).

fof(f346,plain,
    ( sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl9_25
  <=> sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f157,plain,(
    k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f75,f94])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f58,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f210,plain,(
    ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f209,f135])).

fof(f135,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f73,f94])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f209,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f206,f56])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f206,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f67,f183])).

fof(f183,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK4),k2_relat_1(sK5)) ),
    inference(resolution,[],[f180,f136])).

fof(f136,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK4),k1_enumset1(sK3,sK3,sK3)) ),
    inference(extensionality_resolution,[],[f104,f60])).

fof(f60,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f93])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

% (17355)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f180,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))
      | ~ r2_hidden(X0,k2_relat_1(sK5)) ) ),
    inference(subsumption_resolution,[],[f179,f119])).

fof(f119,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f103,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f103,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f93])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK5))
      | v1_xboole_0(k1_enumset1(sK3,sK3,sK3))
      | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) ) ),
    inference(resolution,[],[f166,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f166,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_enumset1(sK3,sK3,sK3))
      | ~ r2_hidden(X0,k2_relat_1(sK5)) ) ),
    inference(resolution,[],[f165,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f165,plain,(
    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3))) ),
    inference(subsumption_resolution,[],[f164,f94])).

fof(f164,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(superposition,[],[f76,f156])).

fof(f156,plain,(
    k2_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k2_relat_1(sK5) ),
    inference(resolution,[],[f74,f94])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

% (17370)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f351,plain,
    ( spl9_25
    | spl9_26 ),
    inference(avatar_split_clause,[],[f342,f348,f344])).

fof(f342,plain,
    ( k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) ),
    inference(subsumption_resolution,[],[f341,f95])).

fof(f95,plain,(
    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f57,f93])).

fof(f57,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f341,plain,
    ( ~ v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3))
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)
    | sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) ),
    inference(resolution,[],[f77,f143])).

fof(f143,plain,(
    sP0(sK2,sK5,k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[],[f81,f94])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

% (17346)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f33])).

fof(f33,plain,(
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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (17343)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.56  % (17349)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (17367)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.57  % (17358)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.57  % (17367)Refutation not found, incomplete strategy% (17367)------------------------------
% 1.42/0.57  % (17367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (17367)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.57  
% 1.66/0.57  % (17367)Memory used [KB]: 10746
% 1.66/0.57  % (17367)Time elapsed: 0.081 s
% 1.66/0.57  % (17367)------------------------------
% 1.66/0.57  % (17367)------------------------------
% 1.66/0.57  % (17350)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.57  % (17349)Refutation found. Thanks to Tanya!
% 1.66/0.57  % SZS status Theorem for theBenchmark
% 1.66/0.57  % (17356)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.58  % (17357)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f408,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(avatar_sat_refutation,[],[f351,f364,f407])).
% 1.66/0.59  fof(f407,plain,(
% 1.66/0.59    ~spl9_26),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f406])).
% 1.66/0.59  fof(f406,plain,(
% 1.66/0.59    $false | ~spl9_26),
% 1.66/0.59    inference(subsumption_resolution,[],[f394,f118])).
% 1.66/0.59  % (17347)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.59  fof(f118,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.66/0.59    inference(resolution,[],[f72,f61])).
% 1.66/0.59  fof(f61,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f2])).
% 1.66/0.59  fof(f2,axiom,(
% 1.66/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.59  fof(f72,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.66/0.59  fof(f394,plain,(
% 1.66/0.59    r2_hidden(sK3,k1_xboole_0) | ~spl9_26),
% 1.66/0.59    inference(superposition,[],[f121,f350])).
% 1.66/0.59  fof(f350,plain,(
% 1.66/0.59    k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | ~spl9_26),
% 1.66/0.59    inference(avatar_component_clause,[],[f348])).
% 1.66/0.59  fof(f348,plain,(
% 1.66/0.59    spl9_26 <=> k1_xboole_0 = k1_enumset1(sK3,sK3,sK3)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.66/0.59  % (17348)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.59  fof(f121,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.66/0.59    inference(resolution,[],[f112,f111])).
% 1.66/0.59  fof(f111,plain,(
% 1.66/0.59    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.66/0.59    inference(equality_resolution,[],[f86])).
% 1.66/0.59  fof(f86,plain,(
% 1.66/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f54])).
% 1.66/0.59  fof(f54,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f52,f53])).
% 1.66/0.59  fof(f53,plain,(
% 1.66/0.59    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f52,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.66/0.59    inference(rectify,[],[f51])).
% 1.66/0.59  fof(f51,plain,(
% 1.66/0.59    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.66/0.59    inference(flattening,[],[f50])).
% 1.66/0.59  fof(f50,plain,(
% 1.66/0.59    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.66/0.59    inference(nnf_transformation,[],[f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.66/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.66/0.59  fof(f112,plain,(
% 1.66/0.59    ( ! [X0,X1] : (sP1(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.66/0.59    inference(equality_resolution,[],[f101])).
% 1.66/0.59  fof(f101,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.66/0.59    inference(definition_unfolding,[],[f91,f65])).
% 1.66/0.59  fof(f65,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.59  fof(f91,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.66/0.59    inference(cnf_transformation,[],[f55])).
% 1.66/0.59  fof(f55,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.66/0.59    inference(nnf_transformation,[],[f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.66/0.59    inference(definition_folding,[],[f4,f35])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.66/0.59  fof(f364,plain,(
% 1.66/0.59    ~spl9_25),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f363])).
% 1.66/0.59  fof(f363,plain,(
% 1.66/0.59    $false | ~spl9_25),
% 1.66/0.59    inference(subsumption_resolution,[],[f359,f59])).
% 1.66/0.59  fof(f59,plain,(
% 1.66/0.59    r2_hidden(sK4,sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f38])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f37])).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.66/0.59    inference(flattening,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.66/0.59    inference(ennf_transformation,[],[f17])).
% 1.66/0.59  fof(f17,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.66/0.59    inference(negated_conjecture,[],[f16])).
% 1.66/0.59  fof(f16,conjecture,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.66/0.59  fof(f359,plain,(
% 1.66/0.59    ~r2_hidden(sK4,sK2) | ~spl9_25),
% 1.66/0.59    inference(backward_demodulation,[],[f210,f352])).
% 1.66/0.59  fof(f352,plain,(
% 1.66/0.59    sK2 = k1_relat_1(sK5) | ~spl9_25),
% 1.66/0.59    inference(backward_demodulation,[],[f157,f346])).
% 1.66/0.59  fof(f346,plain,(
% 1.66/0.59    sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) | ~spl9_25),
% 1.66/0.59    inference(avatar_component_clause,[],[f344])).
% 1.66/0.59  fof(f344,plain,(
% 1.66/0.59    spl9_25 <=> sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.66/0.59  fof(f157,plain,(
% 1.66/0.59    k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f75,f94])).
% 1.66/0.59  fof(f94,plain,(
% 1.66/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))),
% 1.66/0.59    inference(definition_unfolding,[],[f58,f93])).
% 1.66/0.59  fof(f93,plain,(
% 1.66/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.66/0.59    inference(definition_unfolding,[],[f62,f65])).
% 1.66/0.59  fof(f62,plain,(
% 1.66/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.59  fof(f58,plain,(
% 1.66/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.66/0.59    inference(cnf_transformation,[],[f38])).
% 1.66/0.59  fof(f75,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f13])).
% 1.66/0.59  fof(f13,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.66/0.59  fof(f210,plain,(
% 1.66/0.59    ~r2_hidden(sK4,k1_relat_1(sK5))),
% 1.66/0.59    inference(subsumption_resolution,[],[f209,f135])).
% 1.66/0.59  fof(f135,plain,(
% 1.66/0.59    v1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f73,f94])).
% 1.66/0.59  fof(f73,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.59  fof(f209,plain,(
% 1.66/0.59    ~r2_hidden(sK4,k1_relat_1(sK5)) | ~v1_relat_1(sK5)),
% 1.66/0.59    inference(subsumption_resolution,[],[f206,f56])).
% 1.66/0.59  fof(f56,plain,(
% 1.66/0.59    v1_funct_1(sK5)),
% 1.66/0.59    inference(cnf_transformation,[],[f38])).
% 1.66/0.59  fof(f206,plain,(
% 1.66/0.59    ~r2_hidden(sK4,k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f67,f183])).
% 1.66/0.59  fof(f183,plain,(
% 1.66/0.59    ~r2_hidden(k1_funct_1(sK5,sK4),k2_relat_1(sK5))),
% 1.66/0.59    inference(resolution,[],[f180,f136])).
% 1.66/0.59  fof(f136,plain,(
% 1.66/0.59    ~r2_hidden(k1_funct_1(sK5,sK4),k1_enumset1(sK3,sK3,sK3))),
% 1.66/0.59    inference(extensionality_resolution,[],[f104,f60])).
% 1.66/0.59  fof(f60,plain,(
% 1.66/0.59    sK3 != k1_funct_1(sK5,sK4)),
% 1.66/0.59    inference(cnf_transformation,[],[f38])).
% 1.66/0.59  fof(f104,plain,(
% 1.66/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 1.66/0.59    inference(equality_resolution,[],[f99])).
% 1.66/0.59  fof(f99,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.66/0.59    inference(definition_unfolding,[],[f68,f93])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f46])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 1.66/0.59  fof(f45,plain,(
% 1.66/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f44,plain,(
% 1.66/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.59    inference(rectify,[],[f43])).
% 1.66/0.59  % (17355)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.59    inference(nnf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.66/0.59  fof(f180,plain,(
% 1.66/0.59    ( ! [X0] : (r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) | ~r2_hidden(X0,k2_relat_1(sK5))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f179,f119])).
% 1.66/0.59  fof(f119,plain,(
% 1.66/0.59    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 1.66/0.59    inference(resolution,[],[f103,f63])).
% 1.66/0.59  fof(f63,plain,(
% 1.66/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f42])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.59    inference(rectify,[],[f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.59    inference(nnf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.66/0.59  fof(f103,plain,(
% 1.66/0.59    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 1.66/0.59    inference(equality_resolution,[],[f102])).
% 1.66/0.59  fof(f102,plain,(
% 1.66/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 1.66/0.59    inference(equality_resolution,[],[f98])).
% 1.66/0.59  fof(f98,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 1.66/0.59    inference(definition_unfolding,[],[f69,f93])).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f46])).
% 1.66/0.59  fof(f179,plain,(
% 1.66/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK5)) | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))) )),
% 1.66/0.59    inference(resolution,[],[f166,f66])).
% 1.66/0.59  fof(f66,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.66/0.59    inference(flattening,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.66/0.59  fof(f166,plain,(
% 1.66/0.59    ( ! [X0] : (m1_subset_1(X0,k1_enumset1(sK3,sK3,sK3)) | ~r2_hidden(X0,k2_relat_1(sK5))) )),
% 1.66/0.59    inference(resolution,[],[f165,f84])).
% 1.66/0.59  fof(f84,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f32])).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.66/0.59    inference(flattening,[],[f31])).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.66/0.59  fof(f165,plain,(
% 1.66/0.59    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3)))),
% 1.66/0.59    inference(subsumption_resolution,[],[f164,f94])).
% 1.66/0.59  fof(f164,plain,(
% 1.66/0.59    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))),
% 1.66/0.59    inference(superposition,[],[f76,f156])).
% 1.66/0.59  fof(f156,plain,(
% 1.66/0.59    k2_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k2_relat_1(sK5)),
% 1.66/0.59    inference(resolution,[],[f74,f94])).
% 1.66/0.59  fof(f74,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.66/0.59  fof(f76,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.66/0.59  % (17370)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.66/0.59  fof(f351,plain,(
% 1.66/0.59    spl9_25 | spl9_26),
% 1.66/0.59    inference(avatar_split_clause,[],[f342,f348,f344])).
% 1.66/0.59  fof(f342,plain,(
% 1.66/0.59    k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5)),
% 1.66/0.59    inference(subsumption_resolution,[],[f341,f95])).
% 1.66/0.59  fof(f95,plain,(
% 1.66/0.59    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3))),
% 1.66/0.59    inference(definition_unfolding,[],[f57,f93])).
% 1.66/0.59  fof(f57,plain,(
% 1.66/0.59    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.66/0.59    inference(cnf_transformation,[],[f38])).
% 1.66/0.59  fof(f341,plain,(
% 1.66/0.59    ~v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) | sK2 = k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5)),
% 1.66/0.59    inference(resolution,[],[f77,f143])).
% 1.66/0.59  fof(f143,plain,(
% 1.66/0.59    sP0(sK2,sK5,k1_enumset1(sK3,sK3,sK3))),
% 1.66/0.59    inference(resolution,[],[f81,f94])).
% 1.66/0.59  fof(f81,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f49])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(nnf_transformation,[],[f34])).
% 1.66/0.59  % (17346)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(definition_folding,[],[f30,f33])).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.66/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(flattening,[],[f29])).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.59    inference(ennf_transformation,[],[f15])).
% 1.66/0.59  fof(f15,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.66/0.59  fof(f77,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f48])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.66/0.59    inference(rectify,[],[f47])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.66/0.59    inference(nnf_transformation,[],[f33])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (17349)------------------------------
% 1.66/0.59  % (17349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (17349)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (17349)Memory used [KB]: 10874
% 1.66/0.59  % (17349)Time elapsed: 0.147 s
% 1.66/0.59  % (17349)------------------------------
% 1.66/0.59  % (17349)------------------------------
% 1.66/0.60  % (17342)Success in time 0.236 s
%------------------------------------------------------------------------------
