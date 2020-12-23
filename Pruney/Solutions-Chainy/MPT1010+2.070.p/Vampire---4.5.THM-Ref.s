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
% DateTime   : Thu Dec  3 13:05:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 242 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   22
%              Number of atoms          :  351 ( 801 expanded)
%              Number of equality atoms :  134 ( 307 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f183,f209])).

% (11253)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f209,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f200,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f200,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_8 ),
    inference(superposition,[],[f112,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_8
  <=> k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f112,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X0) ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f110,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

% (11253)Refutation not found, incomplete strategy% (11253)------------------------------
% (11253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f95,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(definition_folding,[],[f2,f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f183,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f181,f52])).

fof(f52,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f181,plain,
    ( sK3 = k1_funct_1(sK5,sK4)
    | ~ spl7_7 ),
    inference(resolution,[],[f180,f51])).

fof(f51,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK3 = k1_funct_1(sK5,X0) )
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f159,f179])).

fof(f179,plain,
    ( sK2 = k1_relat_1(sK5)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f127,f173])).

fof(f173,plain,
    ( sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_7
  <=> sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f127,plain,(
    k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f63,f83])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK5))
      | sK3 = k1_funct_1(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f158,f109])).

fof(f109,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f61,f83])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f158,plain,(
    ! [X0] :
      ( sK3 = k1_funct_1(sK5,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK5))
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f157,f48])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f157,plain,(
    ! [X0] :
      ( sK3 = k1_funct_1(sK5,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK5))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f156,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f156,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relat_1(sK5))
      | sK3 = X4 ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X4] :
      ( sK3 = X4
      | sK3 = X4
      | ~ r2_hidden(X4,k2_relat_1(sK5)) ) ),
    inference(resolution,[],[f148,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,k2_relat_1(sK5)) ) ),
    inference(subsumption_resolution,[],[f149,f85])).

fof(f85,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f149,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK5))
      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) ) ),
    inference(resolution,[],[f136,f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f136,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,k2_relat_1(sK5)) ) ),
    inference(resolution,[],[f135,f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f135,plain,(
    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(subsumption_resolution,[],[f134,f83])).

fof(f134,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(superposition,[],[f64,f126])).

fof(f126,plain,(
    k2_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k2_relat_1(sK5) ),
    inference(resolution,[],[f62,f83])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f73,f95])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f178,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f169,f175,f171])).

fof(f169,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) ),
    inference(subsumption_resolution,[],[f168,f84])).

fof(f84,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f49,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,
    ( ~ v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) ),
    inference(resolution,[],[f65,f113])).

fof(f113,plain,(
    sP0(sK2,sK5,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f69,f83])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.53  % (11245)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (11245)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (11261)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f178,f183,f209])).
% 0.22/0.54  % (11253)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    ~spl7_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    $false | ~spl7_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f200,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK3) | ~spl7_8),
% 0.22/0.54    inference(superposition,[],[f112,f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) | ~spl7_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f175])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl7_8 <=> k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X0)) )),
% 0.22/0.54    inference(resolution,[],[f110,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(resolution,[],[f95,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.54    inference(equality_resolution,[],[f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 0.22/0.54  % (11253)Refutation not found, incomplete strategy% (11253)------------------------------
% 0.22/0.54  % (11253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.22/0.54    inference(flattening,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP1(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f79,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f56,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.22/0.54    inference(definition_folding,[],[f2,f35])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ~spl7_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    $false | ~spl7_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f181,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    sK3 != k1_funct_1(sK5,sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    sK3 = k1_funct_1(sK5,sK4) | ~spl7_7),
% 0.22/0.55    inference(resolution,[],[f180,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    r2_hidden(sK4,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = k1_funct_1(sK5,X0)) ) | ~spl7_7),
% 0.22/0.55    inference(backward_demodulation,[],[f159,f179])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    sK2 = k1_relat_1(sK5) | ~spl7_7),
% 0.22/0.55    inference(backward_demodulation,[],[f127,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) | ~spl7_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl7_7 <=> sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5)),
% 0.22/0.55    inference(resolution,[],[f63,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 0.22/0.55    inference(definition_unfolding,[],[f50,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f55,f81])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK5)) | sK3 = k1_funct_1(sK5,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f158,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    v1_relat_1(sK5)),
% 0.22/0.55    inference(resolution,[],[f61,f83])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ( ! [X0] : (sK3 = k1_funct_1(sK5,X0) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_relat_1(sK5)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f157,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    v1_funct_1(sK5)),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ( ! [X0] : (sK3 = k1_funct_1(sK5,X0) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.22/0.55    inference(resolution,[],[f156,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK5)) | sK3 = X4) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ( ! [X4] : (sK3 = X4 | sK3 = X4 | ~r2_hidden(X4,k2_relat_1(sK5))) )),
% 0.22/0.55    inference(resolution,[],[f148,f150])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k2_relat_1(sK5))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f53,f82])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK5)) | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))) )),
% 0.22/0.55    inference(resolution,[],[f136,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k2_relat_1(sK5))) )),
% 0.22/0.55    inference(resolution,[],[f135,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f134,f83])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 0.22/0.55    inference(superposition,[],[f64,f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    k2_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k2_relat_1(sK5)),
% 0.22/0.55    inference(resolution,[],[f62,f83])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.55    inference(resolution,[],[f73,f95])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl7_7 | spl7_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f169,f175,f171])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) | sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f168,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.55    inference(definition_unfolding,[],[f49,f82])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ~v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) | sK2 = k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5)),
% 0.22/0.55    inference(resolution,[],[f65,f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    sP0(sK2,sK5,k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.55    inference(resolution,[],[f69,f83])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(definition_folding,[],[f30,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.55    inference(rectify,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f33])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11245)------------------------------
% 0.22/0.55  % (11245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11245)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11245)Memory used [KB]: 10874
% 0.22/0.55  % (11245)Time elapsed: 0.118 s
% 0.22/0.55  % (11245)------------------------------
% 0.22/0.55  % (11245)------------------------------
% 0.22/0.55  % (11235)Success in time 0.186 s
%------------------------------------------------------------------------------
