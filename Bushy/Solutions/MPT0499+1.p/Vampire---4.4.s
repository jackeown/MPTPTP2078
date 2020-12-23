%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t97_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 196 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  208 ( 442 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f62,f69,f81,f95,f110,f120,f131,f152,f173,f186,f211,f221,f232,f239,f258,f261])).

fof(f261,plain,
    ( ~ spl3_0
    | spl3_5
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f259,f54])).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f259,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f255,f68])).

fof(f68,plain,
    ( k7_relat_1(sK1,sK0) != sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_5
  <=> k7_relat_1(sK1,sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f255,plain,
    ( k7_relat_1(sK1,sK0) = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl3_28 ),
    inference(superposition,[],[f42,f238])).

fof(f238,plain,
    ( k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) = sK1
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_28
  <=> k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t96_relat_1)).

fof(f258,plain,
    ( ~ spl3_0
    | spl3_5
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f256,f54])).

fof(f256,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f254,f68])).

fof(f254,plain,
    ( k7_relat_1(sK1,sK0) = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl3_28 ),
    inference(superposition,[],[f238,f42])).

fof(f239,plain,
    ( spl3_28
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f177,f171,f237])).

fof(f171,plain,
    ( spl3_18
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f177,plain,
    ( k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) = sK1
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f172,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t28_xboole_1)).

fof(f172,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f232,plain,
    ( spl3_26
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f175,f171,f230])).

fof(f230,plain,
    ( spl3_26
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_zfmisc_1(sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f175,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f73,f172,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t1_xboole_1)).

fof(f73,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t3_subset)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',existence_m1_subset_1)).

fof(f221,plain,
    ( spl3_24
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f132,f129,f219])).

fof(f219,plain,
    ( spl3_24
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_relat_1(sK1))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f129,plain,
    ( spl3_14
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f132,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_relat_1(sK1))))),sK0)
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f73,f130,f48])).

fof(f130,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_relat_1(sK1))),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f211,plain,
    ( spl3_22
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f112,f108,f209])).

fof(f209,plain,
    ( spl3_22
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f108,plain,
    ( spl3_10
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f109,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f186,plain,
    ( spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f178,f171,f184])).

fof(f184,plain,
    ( spl3_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f178,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f172,f45])).

fof(f173,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f161,f108,f60,f171])).

fof(f60,plain,
    ( spl3_2
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f161,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f109,f154,f48])).

fof(f154,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),X0),k2_zfmisc_1(sK0,X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t118_zfmisc_1)).

fof(f61,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f152,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f134,f129,f150])).

fof(f150,plain,
    ( spl3_16
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_relat_1(sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f134,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_relat_1(sK1))),k1_zfmisc_1(sK0))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f130,f45])).

fof(f131,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f121,f60,f129])).

fof(f121,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_relat_1(sK1))),sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f73,f61,f48])).

fof(f120,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f100,f93,f118])).

fof(f118,plain,
    ( spl3_12
  <=> k1_relat_1(sK1) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f93,plain,
    ( spl3_8
  <=> k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f94,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',commutativity_k3_xboole_0)).

fof(f94,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f110,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f96,f53,f108])).

fof(f96,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t21_relat_1)).

fof(f95,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f84,f60,f93])).

fof(f84,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f43])).

fof(f81,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f60,f79])).

fof(f79,plain,
    ( spl3_6
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f74,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f45])).

fof(f69,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    k7_relat_1(sK1,sK0) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k7_relat_1(sK1,sK0) != sK1
    & r1_tarski(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != sK1
      & r1_tarski(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k7_relat_1(X1,X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t97_relat_1.p',t97_relat_1)).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f34,f53])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
