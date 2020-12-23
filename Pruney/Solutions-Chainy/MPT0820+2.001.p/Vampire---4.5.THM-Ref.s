%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 229 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  279 ( 476 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f111,f153,f160,f170,f178,f215,f222,f232,f240,f643,f651,f673,f723,f750,f1031])).

fof(f1031,plain,
    ( ~ spl3_6
    | ~ spl3_64
    | ~ spl3_68
    | ~ spl3_71 ),
    inference(avatar_contradiction_clause,[],[f1030])).

fof(f1030,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_64
    | ~ spl3_68
    | ~ spl3_71 ),
    inference(global_subsumption,[],[f61,f1023])).

fof(f1023,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f1006,f592])).

fof(f592,plain,
    ( k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f110,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f110,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1006,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(unit_resulting_resolution,[],[f672,f749,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f749,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f748])).

fof(f748,plain,
    ( spl3_71
  <=> ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f672,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl3_64
  <=> ! [X0] : r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f61,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f38,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(f750,plain,
    ( spl3_71
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f729,f721,f748])).

fof(f721,plain,
    ( spl3_68
  <=> ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f729,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))
    | ~ spl3_68 ),
    inference(superposition,[],[f722,f64])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f722,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f721])).

fof(f723,plain,
    ( spl3_68
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f714,f649,f721])).

fof(f649,plain,
    ( spl3_62
  <=> ! [X0] : m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f714,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))
    | ~ spl3_62 ),
    inference(unit_resulting_resolution,[],[f650,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f650,plain,
    ( ! [X0] : m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0))))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f649])).

fof(f673,plain,
    ( spl3_64
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f664,f641,f671])).

fof(f641,plain,
    ( spl3_60
  <=> ! [X0] : m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f664,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))
    | ~ spl3_60 ),
    inference(unit_resulting_resolution,[],[f642,f51])).

fof(f642,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0))))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f641])).

fof(f651,plain,
    ( spl3_62
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f456,f237,f649])).

fof(f237,plain,
    ( spl3_22
  <=> r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f456,plain,
    ( ! [X0] : m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0))))
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f96,f239,f395])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f239,plain,
    ( r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f237])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f643,plain,
    ( spl3_60
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f452,f175,f641])).

fof(f175,plain,
    ( spl3_14
  <=> r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f452,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0))))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f96,f177,f395])).

fof(f177,plain,
    ( r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f240,plain,
    ( spl3_22
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f234,f229,f237])).

fof(f229,plain,
    ( spl3_21
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f234,plain,
    ( r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f39,f231,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f231,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f232,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f226,f219,f229])).

fof(f219,plain,
    ( spl3_20
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f226,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f221,f52])).

fof(f221,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f216,f212,f108,f219])).

fof(f212,plain,
    ( spl3_19
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f216,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f110,f214,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f214,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f215,plain,
    ( spl3_19
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f208,f69,f212])).

fof(f69,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f208,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f178,plain,
    ( spl3_14
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f172,f167,f175])).

fof(f167,plain,
    ( spl3_13
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f172,plain,
    ( r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f39,f169,f49])).

fof(f169,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f164,f157,f167])).

fof(f157,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f164,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f159,f52])).

fof(f159,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f154,f150,f108,f157])).

fof(f150,plain,
    ( spl3_11
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f154,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f110,f152,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f152,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f146,f69,f150])).

fof(f146,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f71,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f104,f69,f108])).

fof(f104,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f71,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:48:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (21986)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (21977)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21989)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (21974)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (21978)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (21987)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (21985)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (21982)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (21976)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (21979)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (21973)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (21975)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (21981)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (21988)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (21980)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (21983)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (21983)Refutation not found, incomplete strategy% (21983)------------------------------
% 0.21/0.51  % (21983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21983)Memory used [KB]: 10618
% 0.21/0.51  % (21983)Time elapsed: 0.083 s
% 0.21/0.51  % (21983)------------------------------
% 0.21/0.51  % (21983)------------------------------
% 0.21/0.51  % (21972)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (21989)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1125,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f72,f111,f153,f160,f170,f178,f215,f222,f232,f240,f643,f651,f673,f723,f750,f1031])).
% 0.21/0.51  fof(f1031,plain,(
% 0.21/0.51    ~spl3_6 | ~spl3_64 | ~spl3_68 | ~spl3_71),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1030])).
% 0.21/0.51  fof(f1030,plain,(
% 0.21/0.51    $false | (~spl3_6 | ~spl3_64 | ~spl3_68 | ~spl3_71)),
% 0.21/0.51    inference(global_subsumption,[],[f61,f1023])).
% 0.21/0.51  fof(f1023,plain,(
% 0.21/0.51    r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | (~spl3_6 | ~spl3_64 | ~spl3_71)),
% 0.21/0.51    inference(forward_demodulation,[],[f1006,f592])).
% 0.21/0.51  fof(f592,plain,(
% 0.21/0.51    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl3_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f110,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f40,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f44,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f1006,plain,(
% 0.21/0.51    r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | (~spl3_64 | ~spl3_71)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f672,f749,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f59,f60])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))) ) | ~spl3_71),
% 0.21/0.51    inference(avatar_component_clause,[],[f748])).
% 0.21/0.51  fof(f748,plain,(
% 0.21/0.51    spl3_71 <=> ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.21/0.51  fof(f672,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) ) | ~spl3_64),
% 0.21/0.51    inference(avatar_component_clause,[],[f671])).
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    spl3_64 <=> ! [X0] : r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.51    inference(definition_unfolding,[],[f38,f60])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f17])).
% 0.21/0.51  fof(f17,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 0.21/0.51  fof(f750,plain,(
% 0.21/0.51    spl3_71 | ~spl3_68),
% 0.21/0.51    inference(avatar_split_clause,[],[f729,f721,f748])).
% 0.21/0.51  fof(f721,plain,(
% 0.21/0.51    spl3_68 <=> ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.21/0.51  fof(f729,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))) ) | ~spl3_68),
% 0.21/0.51    inference(superposition,[],[f722,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f43,f43])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f722,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) ) | ~spl3_68),
% 0.21/0.51    inference(avatar_component_clause,[],[f721])).
% 0.21/0.51  fof(f723,plain,(
% 0.21/0.51    spl3_68 | ~spl3_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f714,f649,f721])).
% 0.21/0.51  fof(f649,plain,(
% 0.21/0.51    spl3_62 <=> ! [X0] : m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.51  fof(f714,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) ) | ~spl3_62),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f650,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f650,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0))))) ) | ~spl3_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f649])).
% 0.21/0.51  fof(f673,plain,(
% 0.21/0.51    spl3_64 | ~spl3_60),
% 0.21/0.51    inference(avatar_split_clause,[],[f664,f641,f671])).
% 0.21/0.51  fof(f641,plain,(
% 0.21/0.51    spl3_60 <=> ! [X0] : m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.51  fof(f664,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) ) | ~spl3_60),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f642,f51])).
% 0.21/0.51  fof(f642,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0))))) ) | ~spl3_60),
% 0.21/0.51    inference(avatar_component_clause,[],[f641])).
% 0.21/0.51  fof(f651,plain,(
% 0.21/0.51    spl3_62 | ~spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f456,f237,f649])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    spl3_22 <=> r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK1,sK1,X0))))) ) | ~spl3_22),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f239,f395])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~r1_tarski(X2,X1)) )),
% 0.21/0.51    inference(resolution,[],[f58,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f237])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1))))) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f63,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f41,f60])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f643,plain,(
% 0.21/0.51    spl3_60 | ~spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f452,f175,f641])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl3_14 <=> r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f452,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,X0))))) ) | ~spl3_14),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f96,f177,f395])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f175])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl3_22 | ~spl3_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f234,f229,f237])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    spl3_21 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_21),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f39,f231,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f229])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    spl3_21 | ~spl3_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f226,f219,f229])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    spl3_20 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl3_20),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f221,f52])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f219])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    spl3_20 | ~spl3_6 | ~spl3_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f216,f212,f108,f219])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl3_19 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_6 | ~spl3_19)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f110,f214,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    v5_relat_1(sK2,sK1) | ~spl3_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f212])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    spl3_19 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f208,f69,f212])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    v5_relat_1(sK2,sK1) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f71,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl3_14 | ~spl3_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f172,f167,f175])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl3_13 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f39,f169,f49])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl3_13 | ~spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f164,f157,f167])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl3_12 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_12),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f159,f52])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f157])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    spl3_12 | ~spl3_6 | ~spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f154,f150,f108,f157])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl3_11 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_6 | ~spl3_11)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f110,f152,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    v4_relat_1(sK2,sK0) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl3_11 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f146,f69,f150])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v4_relat_1(sK2,sK0) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f71,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl3_6 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f69,f108])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f71,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f69])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21989)------------------------------
% 0.21/0.52  % (21989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21989)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21989)Memory used [KB]: 11641
% 0.21/0.52  % (21989)Time elapsed: 0.075 s
% 0.21/0.52  % (21989)------------------------------
% 0.21/0.52  % (21989)------------------------------
% 0.21/0.52  % (21971)Success in time 0.155 s
%------------------------------------------------------------------------------
