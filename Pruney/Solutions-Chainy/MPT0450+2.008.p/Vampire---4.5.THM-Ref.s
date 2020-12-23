%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 427 expanded)
%              Number of leaves         :   31 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  259 ( 842 expanded)
%              Number of equality atoms :   31 ( 238 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f166,f175,f185,f187,f257,f263])).

fof(f263,plain,
    ( ~ spl4_7
    | ~ spl4_2
    | ~ spl4_9
    | spl4_6 ),
    inference(avatar_split_clause,[],[f188,f164,f182,f88,f169])).

fof(f169,plain,
    ( spl4_7
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f182,plain,
    ( spl4_9
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f164,plain,
    ( spl4_6
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f188,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_6 ),
    inference(resolution,[],[f165,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f165,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f257,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f183,f255])).

fof(f255,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X3) ),
    inference(forward_demodulation,[],[f254,f214])).

fof(f214,plain,(
    ! [X1] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(forward_demodulation,[],[f207,f130])).

fof(f130,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(superposition,[],[f74,f126])).

fof(f126,plain,(
    ! [X4] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X4,X4,X4,k1_xboole_0)) ),
    inference(resolution,[],[f112,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)),X1) ),
    inference(resolution,[],[f111,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f111,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))) ),
    inference(resolution,[],[f77,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f207,plain,(
    ! [X1] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(superposition,[],[f76,f126])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f55,f72,f70,f71])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f254,plain,(
    ! [X2,X3] : r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),X3) ),
    inference(forward_demodulation,[],[f247,f214])).

fof(f247,plain,(
    ! [X2,X3] : r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3))) ),
    inference(superposition,[],[f79,f126])).

fof(f79,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f67,f72,f70,f70,f72])).

fof(f67,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f183,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f174,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f174,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_8
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f185,plain,
    ( ~ spl4_8
    | ~ spl4_3
    | spl4_7 ),
    inference(avatar_split_clause,[],[f179,f169,f92,f173])).

fof(f92,plain,
    ( spl4_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f179,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ spl4_3
    | spl4_7 ),
    inference(resolution,[],[f177,f93])).

fof(f93,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) )
    | spl4_7 ),
    inference(resolution,[],[f176,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_7 ),
    inference(resolution,[],[f170,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f170,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f175,plain,
    ( ~ spl4_7
    | ~ spl4_3
    | ~ spl4_8
    | spl4_5 ),
    inference(avatar_split_clause,[],[f167,f161,f173,f92,f169])).

fof(f161,plain,
    ( spl4_5
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f167,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_5 ),
    inference(resolution,[],[f162,f48])).

% (18021)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f162,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f166,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f156,f84,f164,f161])).

fof(f84,plain,
    ( spl4_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f156,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f80,f85])).

fof(f85,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f94,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f88])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f73,f84])).

fof(f73,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f44,f70,f70])).

fof(f44,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (18009)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (18001)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (18025)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (18005)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (18005)Refutation not found, incomplete strategy% (18005)------------------------------
% 0.21/0.55  % (18005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17997)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (18005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18005)Memory used [KB]: 10618
% 0.21/0.56  % (18005)Time elapsed: 0.118 s
% 0.21/0.56  % (18005)------------------------------
% 0.21/0.56  % (18005)------------------------------
% 0.21/0.58  % (18002)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (18004)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (18004)Refutation not found, incomplete strategy% (18004)------------------------------
% 0.21/0.59  % (18004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (18013)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (17998)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.59  % (17998)Refutation not found, incomplete strategy% (17998)------------------------------
% 1.73/0.59  % (17998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (18000)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.73/0.59  % (17996)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.73/0.59  % (17999)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.73/0.59  % (18011)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.73/0.59  % (17998)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (17998)Memory used [KB]: 10618
% 1.73/0.59  % (17998)Time elapsed: 0.161 s
% 1.73/0.59  % (17998)------------------------------
% 1.73/0.59  % (17998)------------------------------
% 1.73/0.59  % (18017)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.73/0.59  % (18004)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (18004)Memory used [KB]: 10618
% 1.73/0.59  % (18004)Time elapsed: 0.151 s
% 1.73/0.59  % (18004)------------------------------
% 1.73/0.59  % (18004)------------------------------
% 1.73/0.59  % (18007)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.73/0.59  % (18013)Refutation not found, incomplete strategy% (18013)------------------------------
% 1.73/0.59  % (18013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (18013)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (18013)Memory used [KB]: 10618
% 1.73/0.59  % (18013)Time elapsed: 0.155 s
% 1.73/0.59  % (18013)------------------------------
% 1.73/0.59  % (18013)------------------------------
% 1.73/0.60  % (18014)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.73/0.60  % (18022)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.73/0.60  % (18020)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.73/0.60  % (18015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.73/0.61  % (18018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.73/0.61  % (18003)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.73/0.61  % (18006)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.73/0.61  % (18019)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.73/0.61  % (18024)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.91/0.61  % (18010)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.91/0.61  % (18023)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.91/0.61  % (18012)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.91/0.61  % (18008)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.91/0.61  % (18015)Refutation found. Thanks to Tanya!
% 1.91/0.61  % SZS status Theorem for theBenchmark
% 1.91/0.61  % (18016)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.91/0.62  % (18018)Refutation not found, incomplete strategy% (18018)------------------------------
% 1.91/0.62  % (18018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.62  % (18006)Refutation not found, incomplete strategy% (18006)------------------------------
% 1.91/0.62  % (18006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.62  % (18006)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.62  
% 1.91/0.62  % (18006)Memory used [KB]: 10618
% 1.91/0.62  % (18006)Time elapsed: 0.190 s
% 1.91/0.62  % (18006)------------------------------
% 1.91/0.62  % (18006)------------------------------
% 1.91/0.63  % SZS output start Proof for theBenchmark
% 1.91/0.63  fof(f264,plain,(
% 1.91/0.63    $false),
% 1.91/0.63    inference(avatar_sat_refutation,[],[f86,f90,f94,f166,f175,f185,f187,f257,f263])).
% 1.91/0.63  fof(f263,plain,(
% 1.91/0.63    ~spl4_7 | ~spl4_2 | ~spl4_9 | spl4_6),
% 1.91/0.63    inference(avatar_split_clause,[],[f188,f164,f182,f88,f169])).
% 1.91/0.63  fof(f169,plain,(
% 1.91/0.63    spl4_7 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.91/0.63  fof(f88,plain,(
% 1.91/0.63    spl4_2 <=> v1_relat_1(sK1)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.91/0.63  fof(f182,plain,(
% 1.91/0.63    spl4_9 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.91/0.63  fof(f164,plain,(
% 1.91/0.63    spl4_6 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.91/0.63  fof(f188,plain,(
% 1.91/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_6),
% 1.91/0.63    inference(resolution,[],[f165,f48])).
% 1.91/0.63  fof(f48,plain,(
% 1.91/0.63    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f24])).
% 1.91/0.63  fof(f24,plain,(
% 1.91/0.63    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.91/0.63    inference(flattening,[],[f23])).
% 1.91/0.63  fof(f23,plain,(
% 1.91/0.63    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.91/0.63    inference(ennf_transformation,[],[f18])).
% 1.91/0.63  fof(f18,axiom,(
% 1.91/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.91/0.63  fof(f165,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | spl4_6),
% 1.91/0.63    inference(avatar_component_clause,[],[f164])).
% 1.91/0.63  fof(f257,plain,(
% 1.91/0.63    spl4_9),
% 1.91/0.63    inference(avatar_contradiction_clause,[],[f256])).
% 1.91/0.63  fof(f256,plain,(
% 1.91/0.63    $false | spl4_9),
% 1.91/0.63    inference(subsumption_resolution,[],[f183,f255])).
% 1.91/0.63  fof(f255,plain,(
% 1.91/0.63    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X3)) )),
% 1.91/0.63    inference(forward_demodulation,[],[f254,f214])).
% 1.91/0.63  fof(f214,plain,(
% 1.91/0.63    ( ! [X1] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1) )),
% 1.91/0.63    inference(forward_demodulation,[],[f207,f130])).
% 1.91/0.63  fof(f130,plain,(
% 1.91/0.63    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.91/0.63    inference(superposition,[],[f74,f126])).
% 1.91/0.63  fof(f126,plain,(
% 1.91/0.63    ( ! [X4] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X4,X4,X4,k1_xboole_0))) )),
% 1.91/0.63    inference(resolution,[],[f112,f98])).
% 1.91/0.63  fof(f98,plain,(
% 1.91/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.91/0.63    inference(resolution,[],[f60,f46])).
% 1.91/0.63  fof(f46,plain,(
% 1.91/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f7])).
% 1.91/0.63  fof(f7,axiom,(
% 1.91/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.91/0.63  fof(f60,plain,(
% 1.91/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f36])).
% 1.91/0.63  fof(f36,plain,(
% 1.91/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/0.63    inference(flattening,[],[f35])).
% 1.91/0.63  fof(f35,plain,(
% 1.91/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.91/0.63    inference(nnf_transformation,[],[f3])).
% 1.91/0.63  fof(f3,axiom,(
% 1.91/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.91/0.63  fof(f112,plain,(
% 1.91/0.63    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)),X1)) )),
% 1.91/0.63    inference(resolution,[],[f111,f62])).
% 1.91/0.63  fof(f62,plain,(
% 1.91/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f40])).
% 1.91/0.63  fof(f40,plain,(
% 1.91/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.91/0.63  fof(f39,plain,(
% 1.91/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.91/0.63    introduced(choice_axiom,[])).
% 1.91/0.63  fof(f38,plain,(
% 1.91/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/0.63    inference(rectify,[],[f37])).
% 1.91/0.63  fof(f37,plain,(
% 1.91/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/0.63    inference(nnf_transformation,[],[f27])).
% 1.91/0.63  fof(f27,plain,(
% 1.91/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.91/0.63    inference(ennf_transformation,[],[f1])).
% 1.91/0.63  fof(f1,axiom,(
% 1.91/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.91/0.63  fof(f111,plain,(
% 1.91/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)))) )),
% 1.91/0.63    inference(resolution,[],[f77,f45])).
% 1.91/0.63  fof(f45,plain,(
% 1.91/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f11])).
% 1.91/0.63  fof(f11,axiom,(
% 1.91/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.91/0.63  fof(f77,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.91/0.63    inference(definition_unfolding,[],[f57,f70])).
% 1.91/0.63  fof(f70,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.91/0.63    inference(definition_unfolding,[],[f51,f69])).
% 1.91/0.63  fof(f69,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.91/0.63    inference(definition_unfolding,[],[f53,f66])).
% 1.91/0.63  fof(f66,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f13])).
% 1.91/0.63  fof(f13,axiom,(
% 1.91/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.91/0.63  fof(f53,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f12])).
% 1.91/0.63  fof(f12,axiom,(
% 1.91/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.91/0.63  fof(f51,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.91/0.63    inference(cnf_transformation,[],[f15])).
% 1.91/0.63  fof(f15,axiom,(
% 1.91/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.91/0.63  fof(f57,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.91/0.63    inference(cnf_transformation,[],[f34])).
% 1.91/0.63  fof(f34,plain,(
% 1.91/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.91/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f33])).
% 1.91/0.63  fof(f33,plain,(
% 1.91/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.91/0.63    introduced(choice_axiom,[])).
% 1.91/0.63  fof(f26,plain,(
% 1.91/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.91/0.63    inference(ennf_transformation,[],[f21])).
% 1.91/0.63  fof(f21,plain,(
% 1.91/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.91/0.63    inference(rectify,[],[f2])).
% 1.91/0.63  fof(f2,axiom,(
% 1.91/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.91/0.63  fof(f74,plain,(
% 1.91/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = X0) )),
% 1.91/0.63    inference(definition_unfolding,[],[f47,f71])).
% 1.91/0.63  fof(f71,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.91/0.63    inference(definition_unfolding,[],[f54,f70])).
% 1.91/0.63  fof(f54,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.91/0.63    inference(cnf_transformation,[],[f4])).
% 1.91/0.63  fof(f4,axiom,(
% 1.91/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.91/0.63  fof(f47,plain,(
% 1.91/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.91/0.63    inference(cnf_transformation,[],[f9])).
% 1.91/0.63  fof(f9,axiom,(
% 1.91/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.91/0.63  fof(f207,plain,(
% 1.91/0.63    ( ! [X1] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) = X1) )),
% 1.91/0.63    inference(superposition,[],[f76,f126])).
% 1.91/0.63  fof(f76,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = X0) )),
% 1.91/0.63    inference(definition_unfolding,[],[f55,f72,f70,f71])).
% 1.91/0.63  fof(f72,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.91/0.63    inference(definition_unfolding,[],[f52,f69])).
% 1.91/0.63  fof(f52,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f14])).
% 1.91/0.63  fof(f14,axiom,(
% 1.91/0.63    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.91/0.63  fof(f55,plain,(
% 1.91/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.91/0.63    inference(cnf_transformation,[],[f10])).
% 1.91/0.63  fof(f10,axiom,(
% 1.91/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.91/0.63  fof(f254,plain,(
% 1.91/0.63    ( ! [X2,X3] : (r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),X3)) )),
% 1.91/0.63    inference(forward_demodulation,[],[f247,f214])).
% 1.91/0.63  fof(f247,plain,(
% 1.91/0.63    ( ! [X2,X3] : (r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3)))) )),
% 1.91/0.63    inference(superposition,[],[f79,f126])).
% 1.91/0.63  fof(f79,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.91/0.63    inference(definition_unfolding,[],[f67,f72,f70,f70,f72])).
% 1.91/0.63  fof(f67,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.91/0.63    inference(cnf_transformation,[],[f8])).
% 1.91/0.63  fof(f8,axiom,(
% 1.91/0.63    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.91/0.63  fof(f183,plain,(
% 1.91/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl4_9),
% 1.91/0.63    inference(avatar_component_clause,[],[f182])).
% 1.91/0.63  fof(f187,plain,(
% 1.91/0.63    spl4_8),
% 1.91/0.63    inference(avatar_contradiction_clause,[],[f186])).
% 1.91/0.63  fof(f186,plain,(
% 1.91/0.63    $false | spl4_8),
% 1.91/0.63    inference(resolution,[],[f174,f75])).
% 1.91/0.63  fof(f75,plain,(
% 1.91/0.63    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.91/0.63    inference(definition_unfolding,[],[f50,f70])).
% 1.91/0.63  fof(f50,plain,(
% 1.91/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f5])).
% 1.91/0.63  fof(f5,axiom,(
% 1.91/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.91/0.63  fof(f174,plain,(
% 1.91/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl4_8),
% 1.91/0.63    inference(avatar_component_clause,[],[f173])).
% 1.91/0.63  fof(f173,plain,(
% 1.91/0.63    spl4_8 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.91/0.63  fof(f185,plain,(
% 1.91/0.63    ~spl4_8 | ~spl4_3 | spl4_7),
% 1.91/0.63    inference(avatar_split_clause,[],[f179,f169,f92,f173])).
% 1.91/0.63  fof(f92,plain,(
% 1.91/0.63    spl4_3 <=> v1_relat_1(sK0)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.91/0.63  fof(f179,plain,(
% 1.91/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | (~spl4_3 | spl4_7)),
% 1.91/0.63    inference(resolution,[],[f177,f93])).
% 1.91/0.63  fof(f93,plain,(
% 1.91/0.63    v1_relat_1(sK0) | ~spl4_3),
% 1.91/0.63    inference(avatar_component_clause,[],[f92])).
% 1.91/0.63  fof(f177,plain,(
% 1.91/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)) ) | spl4_7),
% 1.91/0.63    inference(resolution,[],[f176,f65])).
% 1.91/0.63  fof(f65,plain,(
% 1.91/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f41])).
% 1.91/0.63  fof(f41,plain,(
% 1.91/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.91/0.63    inference(nnf_transformation,[],[f16])).
% 1.91/0.63  fof(f16,axiom,(
% 1.91/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.91/0.63  fof(f176,plain,(
% 1.91/0.63    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_7),
% 1.91/0.63    inference(resolution,[],[f170,f49])).
% 1.91/0.63  fof(f49,plain,(
% 1.91/0.63    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f25])).
% 1.91/0.63  fof(f25,plain,(
% 1.91/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.91/0.63    inference(ennf_transformation,[],[f17])).
% 1.91/0.63  fof(f17,axiom,(
% 1.91/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.91/0.63  fof(f170,plain,(
% 1.91/0.63    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_7),
% 1.91/0.63    inference(avatar_component_clause,[],[f169])).
% 1.91/0.63  fof(f175,plain,(
% 1.91/0.63    ~spl4_7 | ~spl4_3 | ~spl4_8 | spl4_5),
% 1.91/0.63    inference(avatar_split_clause,[],[f167,f161,f173,f92,f169])).
% 1.91/0.63  fof(f161,plain,(
% 1.91/0.63    spl4_5 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.91/0.63  fof(f167,plain,(
% 1.91/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_5),
% 1.91/0.63    inference(resolution,[],[f162,f48])).
% 1.91/0.63  % (18021)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.91/0.63  fof(f162,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl4_5),
% 1.91/0.63    inference(avatar_component_clause,[],[f161])).
% 1.91/0.63  fof(f166,plain,(
% 1.91/0.63    ~spl4_5 | ~spl4_6 | spl4_1),
% 1.91/0.63    inference(avatar_split_clause,[],[f156,f84,f164,f161])).
% 1.91/0.63  fof(f84,plain,(
% 1.91/0.63    spl4_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.91/0.63  fof(f156,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl4_1),
% 1.91/0.63    inference(resolution,[],[f80,f85])).
% 1.91/0.63  fof(f85,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) | spl4_1),
% 1.91/0.63    inference(avatar_component_clause,[],[f84])).
% 1.91/0.63  fof(f80,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.91/0.63    inference(definition_unfolding,[],[f68,f70])).
% 1.91/0.63  fof(f68,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f29])).
% 1.91/0.63  fof(f29,plain,(
% 1.91/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.91/0.63    inference(flattening,[],[f28])).
% 1.91/0.63  fof(f28,plain,(
% 1.91/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.91/0.63    inference(ennf_transformation,[],[f6])).
% 1.91/0.63  fof(f6,axiom,(
% 1.91/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.91/0.63  fof(f94,plain,(
% 1.91/0.63    spl4_3),
% 1.91/0.63    inference(avatar_split_clause,[],[f42,f92])).
% 1.91/0.63  fof(f42,plain,(
% 1.91/0.63    v1_relat_1(sK0)),
% 1.91/0.63    inference(cnf_transformation,[],[f32])).
% 1.91/0.63  fof(f32,plain,(
% 1.91/0.63    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.91/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f31,f30])).
% 1.91/0.63  fof(f30,plain,(
% 1.91/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.91/0.63    introduced(choice_axiom,[])).
% 1.91/0.63  fof(f31,plain,(
% 1.91/0.63    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.91/0.63    introduced(choice_axiom,[])).
% 1.91/0.63  fof(f22,plain,(
% 1.91/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.91/0.63    inference(ennf_transformation,[],[f20])).
% 1.91/0.63  fof(f20,negated_conjecture,(
% 1.91/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.91/0.63    inference(negated_conjecture,[],[f19])).
% 1.91/0.63  fof(f19,conjecture,(
% 1.91/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 1.91/0.63  fof(f90,plain,(
% 1.91/0.63    spl4_2),
% 1.91/0.63    inference(avatar_split_clause,[],[f43,f88])).
% 1.91/0.63  fof(f43,plain,(
% 1.91/0.63    v1_relat_1(sK1)),
% 1.91/0.63    inference(cnf_transformation,[],[f32])).
% 1.91/0.63  fof(f86,plain,(
% 1.91/0.63    ~spl4_1),
% 1.91/0.63    inference(avatar_split_clause,[],[f73,f84])).
% 1.91/0.63  fof(f73,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 1.91/0.63    inference(definition_unfolding,[],[f44,f70,f70])).
% 1.91/0.63  fof(f44,plain,(
% 1.91/0.63    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 1.91/0.63    inference(cnf_transformation,[],[f32])).
% 1.91/0.63  % SZS output end Proof for theBenchmark
% 1.91/0.63  % (18015)------------------------------
% 1.91/0.63  % (18015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.63  % (18015)Termination reason: Refutation
% 1.91/0.63  
% 1.91/0.63  % (18015)Memory used [KB]: 10874
% 1.91/0.63  % (18015)Time elapsed: 0.188 s
% 1.91/0.63  % (18015)------------------------------
% 1.91/0.63  % (18015)------------------------------
% 1.91/0.63  % (17995)Success in time 0.259 s
%------------------------------------------------------------------------------
