%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 224 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 433 expanded)
%              Number of equality atoms :   66 ( 165 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f70,f225,f331,f333])).

fof(f333,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f254,f62,f211])).

fof(f211,plain,
    ( spl3_5
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f62,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f254,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f253,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k3_xboole_0(X0,sK0) = X0 )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k3_xboole_0(X0,sK0) = X0
        | k3_xboole_0(X0,sK0) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f249,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f249,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | k3_xboole_0(X0,sK0) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f206,f45])).

fof(f206,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK2(X2,sK0),X3)
        | k3_xboole_0(X2,sK0) = X2
        | ~ r1_tarski(X3,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f202,f44])).

% (29886)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK0),sK1)
        | k3_xboole_0(X0,sK0) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f144,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK2(X2,X1),X0)
      | k3_xboole_0(X2,X1) = X2 ) ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK2(X0,X1),X2) ) ),
    inference(resolution,[],[f43,f46])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f331,plain,
    ( spl3_3
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f329,f223,f62,f68])).

fof(f68,plain,
    ( spl3_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (29868)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f223,plain,
    ( spl3_6
  <=> sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f329,plain,
    ( sK0 = k4_subset_1(sK0,sK1,sK0)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f328,f224])).

fof(f224,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f223])).

fof(f328,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f326,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f326,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f242,f63])).

fof(f242,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_tarski(k2_enumset1(X2,X2,X2,X1)) = k4_subset_1(X1,X2,X1) ) ),
    inference(resolution,[],[f56,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f225,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f221,f211,f223])).

fof(f221,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f220,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f220,plain,
    ( k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f216,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f100,f80])).

fof(f80,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = X1 ),
    inference(superposition,[],[f74,f54])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = X0 ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) ),
    inference(superposition,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f36,f40,f50])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f216,plain,
    ( k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k5_xboole_0(sK1,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f55,f212])).

fof(f212,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f211])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f41,f50,f40,f50])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f70,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f66,f58,f68])).

fof(f58,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f59,f32])).

fof(f59,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:21:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29864)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (29880)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (29867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (29870)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29872)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (29870)Refutation not found, incomplete strategy% (29870)------------------------------
% 0.21/0.53  % (29870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29870)Memory used [KB]: 10618
% 0.21/0.53  % (29872)Refutation not found, incomplete strategy% (29872)------------------------------
% 0.21/0.53  % (29872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29880)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (29872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29872)Memory used [KB]: 10746
% 0.21/0.53  % (29872)Time elapsed: 0.118 s
% 0.21/0.53  % (29872)------------------------------
% 0.21/0.53  % (29872)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f60,f64,f70,f225,f331,f333])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    spl3_5 | ~spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f254,f62,f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl3_5 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f253,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f46,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k3_xboole_0(X0,sK0) = X0) ) | ~spl3_2),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | k3_xboole_0(X0,sK0) = X0 | k3_xboole_0(X0,sK0) = X0) ) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f249,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,sK0) | ~r1_tarski(X0,sK1) | k3_xboole_0(X0,sK0) = X0) ) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f206,f45])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(sK2(X2,sK0),X3) | k3_xboole_0(X2,sK0) = X2 | ~r1_tarski(X3,sK1)) ) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f202,f44])).
% 0.21/0.54  % (29886)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK2(X0,sK0),sK1) | k3_xboole_0(X0,sK0) = X0) ) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f144,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f62])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(sK2(X2,X1),X0) | k3_xboole_0(X2,X1) = X2) )),
% 0.21/0.54    inference(resolution,[],[f77,f42])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(sK2(X0,X1),X2)) )),
% 0.21/0.54    inference(resolution,[],[f43,f46])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    spl3_3 | ~spl3_2 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f329,f223,f62,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl3_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  % (29868)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    spl3_6 <=> sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    sK0 = k4_subset_1(sK0,sK1,sK0) | (~spl3_2 | ~spl3_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f328,f224])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f223])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl3_2),
% 0.21/0.54    inference(forward_demodulation,[],[f326,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f49,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | ~spl3_2),
% 0.21/0.54    inference(resolution,[],[f242,f63])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_tarski(k2_enumset1(X2,X2,X2,X1)) = k4_subset_1(X1,X2,X1)) )),
% 0.21/0.54    inference(resolution,[],[f56,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f34,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f49])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    spl3_6 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f221,f211,f223])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl3_5),
% 0.21/0.54    inference(forward_demodulation,[],[f220,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f50])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0)) | ~spl3_5),
% 0.21/0.54    inference(forward_demodulation,[],[f216,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f100,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k3_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = X1) )),
% 0.21/0.54    inference(superposition,[],[f74,f54])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = X0) )),
% 0.21/0.54    inference(resolution,[],[f52,f42])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f50])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))))) )),
% 0.21/0.54    inference(superposition,[],[f53,f54])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f40,f50])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k5_xboole_0(sK1,sK1))) | ~spl3_5),
% 0.21/0.54    inference(superposition,[],[f55,f212])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f211])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f41,f50,f40,f50])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ~spl3_3 | spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f66,f58,f68])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_1),
% 0.21/0.54    inference(forward_demodulation,[],[f59,f32])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f58])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f62])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ~spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f58])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (29880)------------------------------
% 0.21/0.54  % (29880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29880)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (29880)Memory used [KB]: 10874
% 0.21/0.54  % (29880)Time elapsed: 0.124 s
% 0.21/0.54  % (29880)------------------------------
% 0.21/0.54  % (29880)------------------------------
% 0.21/0.54  % (29861)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (29889)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29861)Refutation not found, incomplete strategy% (29861)------------------------------
% 0.21/0.54  % (29861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29861)Memory used [KB]: 1663
% 0.21/0.54  % (29861)Time elapsed: 0.123 s
% 0.21/0.54  % (29861)------------------------------
% 0.21/0.54  % (29861)------------------------------
% 0.21/0.54  % (29863)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (29860)Success in time 0.175 s
%------------------------------------------------------------------------------
