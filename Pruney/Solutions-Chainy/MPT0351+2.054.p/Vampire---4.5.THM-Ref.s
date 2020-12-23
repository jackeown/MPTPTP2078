%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 228 expanded)
%              Number of leaves         :   41 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  378 ( 590 expanded)
%              Number of equality atoms :   82 ( 133 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f74,f79,f83,f87,f91,f95,f101,f111,f115,f119,f156,f164,f170,f181,f185,f192,f204,f207,f213,f231,f257,f263])).

fof(f263,plain,
    ( ~ spl3_1
    | spl3_21
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_1
    | spl3_21
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f261,f169])).

fof(f169,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_21
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f261,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f258,f230])).

fof(f230,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl3_30
  <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f258,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_1
    | ~ spl3_34 ),
    inference(resolution,[],[f256,f65])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f256,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_34
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f257,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f233,f179,f72,f255])).

fof(f72,plain,
    ( spl3_3
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f179,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f233,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) )
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f180,f73])).

fof(f73,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f179])).

fof(f231,plain,
    ( spl3_30
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f216,f210,f99,f228])).

fof(f99,plain,
    ( spl3_9
  <=> ! [X1,X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

% (25731)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f210,plain,
    ( spl3_28
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f216,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(superposition,[],[f100,f212])).

fof(f212,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f210])).

fof(f100,plain,
    ( ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f213,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f208,f198,f85,f210])).

fof(f85,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f198,plain,
    ( spl3_26
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f208,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(resolution,[],[f200,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f200,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f198])).

fof(f207,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f205,f65])).

fof(f205,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f203,f73])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f204,plain,
    ( spl3_26
    | spl3_27
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f193,f190,f63,f202,f198])).

fof(f190,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r1_tarski(sK1,sK0)
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X0)) )
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(resolution,[],[f191,f65])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl3_25
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f188,f183,f113,f190])).

fof(f113,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r2_hidden(sK2(X0,X1,X2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f183,plain,
    ( spl3_24
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | r2_hidden(sK2(X2,X0,X1),X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(resolution,[],[f184,f114])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f184,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK2(X2,X0,X1),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3)) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl3_24
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f120,f109,f89,f183])).

fof(f89,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | r2_hidden(sK2(X2,X0,X1),X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3)) )
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f110,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f181,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f59,f179])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f170,plain,
    ( ~ spl3_21
    | spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f165,f161,f76,f167])).

fof(f76,plain,
    ( spl3_4
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( spl3_20
  <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f165,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f78,f163])).

fof(f163,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f78,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f164,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f158,f154,f72,f161])).

fof(f154,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f158,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(resolution,[],[f155,f73])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f150,f117,f63,f154])).

fof(f117,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1) )
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f118,f65])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f47,f117])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f115,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f44,f113])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK2(X0,X1,X2),X2)
            & r2_hidden(sK2(X0,X1,X2),X1)
            & m1_subset_1(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f111,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f43,f109])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f96,f93,f81,f99])).

fof(f81,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f94,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,
    ( ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f58,f93])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f91,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f87,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f60,f76])).

fof(f60,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f74,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f61,f72])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (25729)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (25724)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (25735)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (25732)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (25736)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (25742)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (25733)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (25730)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (25737)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (25732)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (25727)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (25741)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f265,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f66,f74,f79,f83,f87,f91,f95,f101,f111,f115,f119,f156,f164,f170,f181,f185,f192,f204,f207,f213,f231,f257,f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    ~spl3_1 | spl3_21 | ~spl3_30 | ~spl3_34),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f262])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    $false | (~spl3_1 | spl3_21 | ~spl3_30 | ~spl3_34)),
% 0.22/0.49    inference(subsumption_resolution,[],[f261,f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    sK0 != k4_subset_1(sK0,sK0,sK1) | spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f167])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl3_21 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl3_1 | ~spl3_30 | ~spl3_34)),
% 0.22/0.49    inference(forward_demodulation,[],[f258,f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    spl3_30 <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl3_1 | ~spl3_34)),
% 0.22/0.49    inference(resolution,[],[f256,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ) | ~spl3_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f255])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    spl3_34 <=> ! [X1,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    spl3_34 | ~spl3_3 | ~spl3_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f233,f179,f72,f255])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl3_3 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl3_23 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X2,X1) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ) | (~spl3_3 | ~spl3_23)),
% 0.22/0.49    inference(resolution,[],[f180,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) | ~spl3_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f179])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl3_30 | ~spl3_9 | ~spl3_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f216,f210,f99,f228])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl3_9 <=> ! [X1,X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  % (25731)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl3_28 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl3_9 | ~spl3_28)),
% 0.22/0.49    inference(superposition,[],[f100,f212])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f210])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl3_28 | ~spl3_6 | ~spl3_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f208,f198,f85,f210])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl3_26 <=> r1_tarski(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    sK1 = k3_xboole_0(sK1,sK0) | (~spl3_6 | ~spl3_26)),
% 0.22/0.49    inference(resolution,[],[f200,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    r1_tarski(sK1,sK0) | ~spl3_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f198])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_3 | ~spl3_27),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_3 | ~spl3_27)),
% 0.22/0.49    inference(subsumption_resolution,[],[f205,f65])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_27)),
% 0.22/0.49    inference(resolution,[],[f203,f73])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl3_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f202])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    spl3_27 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(sK0,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    spl3_26 | spl3_27 | ~spl3_1 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f193,f190,f63,f202,f198])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r1_tarski(sK1,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(X0))) ) | (~spl3_1 | ~spl3_25)),
% 0.22/0.49    inference(resolution,[],[f191,f65])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f190])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl3_25 | ~spl3_12 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f188,f183,f113,f190])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl3_12 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    spl3_24 <=> ! [X1,X3,X0,X2] : (r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK2(X2,X0,X1),X3) | ~m1_subset_1(X0,k1_zfmisc_1(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl3_12 | ~spl3_24)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f186])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) ) | (~spl3_12 | ~spl3_24)),
% 0.22/0.49    inference(resolution,[],[f184,f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f113])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X2,X0,X1),X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X3))) ) | ~spl3_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f183])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl3_24 | ~spl3_7 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f120,f109,f89,f183])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl3_7 <=> ! [X1,X0,X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK2(X2,X0,X1),X3) | ~m1_subset_1(X0,k1_zfmisc_1(X3))) ) | (~spl3_7 | ~spl3_11)),
% 0.22/0.49    inference(resolution,[],[f110,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f109])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    spl3_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f59,f179])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f46,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f38,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f39,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f48,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f49,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f50,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~spl3_21 | spl3_4 | ~spl3_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f165,f161,f76,f167])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_4 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl3_20 <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    sK0 != k4_subset_1(sK0,sK0,sK1) | (spl3_4 | ~spl3_20)),
% 0.22/0.49    inference(superposition,[],[f78,f163])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl3_20 | ~spl3_3 | ~spl3_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f158,f154,f72,f161])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl3_19 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | (~spl3_3 | ~spl3_19)),
% 0.22/0.49    inference(resolution,[],[f155,f73])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1)) ) | ~spl3_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f154])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl3_19 | ~spl3_1 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f117,f63,f154])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl3_13 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k4_subset_1(sK0,X0,sK1)) ) | (~spl3_1 | ~spl3_13)),
% 0.22/0.49    inference(resolution,[],[f118,f65])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)) ) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f117])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f117])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl3_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f113])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f109])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl3_9 | ~spl3_5 | ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f93,f81,f99])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_8 <=> ! [X1,X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0) ) | (~spl3_5 | ~spl3_8)),
% 0.22/0.49    inference(superposition,[],[f94,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) ) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f93])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.22/0.49    inference(definition_unfolding,[],[f37,f57])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f89])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f85])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f81])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f60,f76])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.22/0.49    inference(backward_demodulation,[],[f33,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f17])).
% 0.22/0.49  fof(f17,conjecture,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f61,f72])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f35,f34])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (25732)------------------------------
% 0.22/0.49  % (25732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25732)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (25732)Memory used [KB]: 6268
% 0.22/0.49  % (25732)Time elapsed: 0.016 s
% 0.22/0.49  % (25732)------------------------------
% 0.22/0.49  % (25732)------------------------------
% 0.22/0.49  % (25738)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (25723)Success in time 0.13 s
%------------------------------------------------------------------------------
