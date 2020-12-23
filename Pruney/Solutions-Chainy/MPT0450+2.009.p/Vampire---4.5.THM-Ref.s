%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 575 expanded)
%              Number of leaves         :   30 ( 191 expanded)
%              Depth                    :   15
%              Number of atoms          :  260 (1002 expanded)
%              Number of equality atoms :   31 ( 371 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f163,f177,f180,f183,f194,f203,f206,f265])).

fof(f265,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f226,f202])).

fof(f202,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_9
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f226,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X3) ),
    inference(forward_demodulation,[],[f225,f188])).

fof(f188,plain,(
    ! [X1] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(forward_demodulation,[],[f186,f139])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f74,f134])).

fof(f134,plain,(
    ! [X7] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X7,X7,X7,k1_xboole_0)) ),
    inference(resolution,[],[f128,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f128,plain,(
    ! [X4,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,k1_xboole_0)),X4) ),
    inference(resolution,[],[f99,f97])).

fof(f97,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f75,f74])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f70])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2) ) ),
    inference(resolution,[],[f78,f62])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f70])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f186,plain,(
    ! [X1] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(superposition,[],[f77,f134])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f225,plain,(
    ! [X2,X3] : r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),X3) ),
    inference(forward_demodulation,[],[f219,f188])).

fof(f219,plain,(
    ! [X2,X3] : r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3))) ),
    inference(superposition,[],[f80,f134])).

fof(f80,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f67,f72,f70,f70,f72])).

fof(f67,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f206,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f198,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f198,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f203,plain,
    ( ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_4 ),
    inference(avatar_split_clause,[],[f184,f160,f200,f196,f166])).

fof(f166,plain,
    ( spl4_5
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( spl4_4
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f184,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_4 ),
    inference(resolution,[],[f162,f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f162,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f194,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f190,f76])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f190,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl4_5 ),
    inference(resolution,[],[f189,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) )
    | spl4_5 ),
    inference(resolution,[],[f181,f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_5 ),
    inference(resolution,[],[f168,f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f168,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f183,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f176,f76])).

fof(f176,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_7
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f180,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f172,f42])).

fof(f172,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f177,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f164,f156,f174,f170,f166])).

fof(f156,plain,
    ( spl4_3
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f164,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl4_3 ),
    inference(resolution,[],[f158,f47])).

fof(f158,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f163,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f151,f160,f156])).

fof(f151,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f81,f73])).

fof(f73,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f44,f70,f70])).

fof(f44,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (5953)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (5938)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (5938)Refutation not found, incomplete strategy% (5938)------------------------------
% 0.21/0.55  % (5938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5945)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (5937)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (5952)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (5954)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (5936)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (5946)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (5938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5938)Memory used [KB]: 10618
% 0.21/0.55  % (5938)Time elapsed: 0.102 s
% 0.21/0.55  % (5938)------------------------------
% 0.21/0.55  % (5938)------------------------------
% 0.21/0.56  % (5944)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (5952)Refutation not found, incomplete strategy% (5952)------------------------------
% 0.21/0.57  % (5952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5952)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5952)Memory used [KB]: 10746
% 0.21/0.57  % (5952)Time elapsed: 0.141 s
% 0.21/0.57  % (5952)------------------------------
% 0.21/0.57  % (5952)------------------------------
% 0.21/0.59  % (5932)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (5939)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (5932)Refutation not found, incomplete strategy% (5932)------------------------------
% 0.21/0.59  % (5932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (5932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (5932)Memory used [KB]: 10618
% 0.21/0.59  % (5932)Time elapsed: 0.159 s
% 0.21/0.59  % (5932)------------------------------
% 0.21/0.59  % (5932)------------------------------
% 0.21/0.59  % (5931)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (5947)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (5947)Refutation not found, incomplete strategy% (5947)------------------------------
% 0.21/0.59  % (5947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (5934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (5947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (5947)Memory used [KB]: 10618
% 0.21/0.59  % (5947)Time elapsed: 0.122 s
% 0.21/0.59  % (5947)------------------------------
% 0.21/0.59  % (5947)------------------------------
% 1.55/0.60  % (5941)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.60  % (5939)Refutation not found, incomplete strategy% (5939)------------------------------
% 1.55/0.60  % (5939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (5939)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (5939)Memory used [KB]: 10618
% 1.55/0.60  % (5939)Time elapsed: 0.122 s
% 1.55/0.60  % (5939)------------------------------
% 1.55/0.60  % (5939)------------------------------
% 1.55/0.60  % (5933)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.55/0.60  % (5956)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.61  % (5949)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.55/0.61  % (5950)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.55/0.61  % (5948)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.61  % (5958)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.55/0.61  % (5957)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.55/0.61  % (5942)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.90/0.61  % (5930)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.90/0.61  % (5955)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.90/0.61  % (5940)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.90/0.61  % (5940)Refutation not found, incomplete strategy% (5940)------------------------------
% 1.90/0.61  % (5940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (5940)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (5940)Memory used [KB]: 10618
% 1.90/0.61  % (5940)Time elapsed: 0.181 s
% 1.90/0.61  % (5940)------------------------------
% 1.90/0.61  % (5940)------------------------------
% 1.90/0.62  % (5942)Refutation found. Thanks to Tanya!
% 1.90/0.62  % SZS status Theorem for theBenchmark
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  fof(f269,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f163,f177,f180,f183,f194,f203,f206,f265])).
% 1.90/0.62  fof(f265,plain,(
% 1.90/0.62    spl4_9),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f257])).
% 1.90/0.62  fof(f257,plain,(
% 1.90/0.62    $false | spl4_9),
% 1.90/0.62    inference(resolution,[],[f226,f202])).
% 1.90/0.62  fof(f202,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl4_9),
% 1.90/0.62    inference(avatar_component_clause,[],[f200])).
% 1.90/0.62  fof(f200,plain,(
% 1.90/0.62    spl4_9 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.90/0.62  fof(f226,plain,(
% 1.90/0.62    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X3)) )),
% 1.90/0.62    inference(forward_demodulation,[],[f225,f188])).
% 1.90/0.62  fof(f188,plain,(
% 1.90/0.62    ( ! [X1] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1) )),
% 1.90/0.62    inference(forward_demodulation,[],[f186,f139])).
% 1.90/0.62  fof(f139,plain,(
% 1.90/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.90/0.62    inference(backward_demodulation,[],[f74,f134])).
% 1.90/0.62  fof(f134,plain,(
% 1.90/0.62    ( ! [X7] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X7,X7,X7,k1_xboole_0))) )),
% 1.90/0.62    inference(resolution,[],[f128,f87])).
% 1.90/0.62  fof(f87,plain,(
% 1.90/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.90/0.62    inference(resolution,[],[f60,f45])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f7])).
% 1.90/0.62  fof(f7,axiom,(
% 1.90/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.90/0.62  fof(f60,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f36])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.62    inference(flattening,[],[f35])).
% 1.90/0.62  fof(f35,plain,(
% 1.90/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.62    inference(nnf_transformation,[],[f3])).
% 1.90/0.62  fof(f3,axiom,(
% 1.90/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.90/0.62  fof(f128,plain,(
% 1.90/0.62    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,k1_xboole_0)),X4)) )),
% 1.90/0.62    inference(resolution,[],[f99,f97])).
% 1.90/0.62  fof(f97,plain,(
% 1.90/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.90/0.62    inference(superposition,[],[f75,f74])).
% 1.90/0.62  fof(f75,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f49,f71])).
% 1.90/0.62  fof(f71,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f54,f70])).
% 1.90/0.62  fof(f70,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f51,f69])).
% 1.90/0.62  fof(f69,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f53,f66])).
% 1.90/0.62  fof(f66,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f13])).
% 1.90/0.62  fof(f13,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.90/0.62  fof(f53,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f12])).
% 1.90/0.62  fof(f12,axiom,(
% 1.90/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.90/0.62  fof(f51,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f15])).
% 1.90/0.62  fof(f15,axiom,(
% 1.90/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.90/0.62  fof(f54,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.90/0.62  fof(f99,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)) )),
% 1.90/0.62    inference(resolution,[],[f78,f62])).
% 1.90/0.62  fof(f62,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f40])).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.90/0.62  fof(f39,plain,(
% 1.90/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f38,plain,(
% 1.90/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.90/0.62    inference(rectify,[],[f37])).
% 1.90/0.62  fof(f37,plain,(
% 1.90/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.90/0.62    inference(nnf_transformation,[],[f27])).
% 1.90/0.62  fof(f27,plain,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f1])).
% 1.90/0.62  fof(f1,axiom,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.90/0.62  fof(f78,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f57,f70])).
% 1.90/0.62  fof(f57,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f34])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f33])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f26,plain,(
% 1.90/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f21])).
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(rectify,[],[f2])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.90/0.62  fof(f74,plain,(
% 1.90/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = X0) )),
% 1.90/0.62    inference(definition_unfolding,[],[f46,f71])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f9])).
% 1.90/0.62  fof(f9,axiom,(
% 1.90/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.90/0.62  fof(f186,plain,(
% 1.90/0.62    ( ! [X1] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) = X1) )),
% 1.90/0.62    inference(superposition,[],[f77,f134])).
% 1.90/0.62  fof(f77,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = X0) )),
% 1.90/0.62    inference(definition_unfolding,[],[f55,f72,f70,f71])).
% 1.90/0.62  fof(f72,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f52,f69])).
% 1.90/0.62  fof(f52,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f14])).
% 1.90/0.62  fof(f14,axiom,(
% 1.90/0.62    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.90/0.62  fof(f55,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.90/0.62  fof(f225,plain,(
% 1.90/0.62    ( ! [X2,X3] : (r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),X3)) )),
% 1.90/0.62    inference(forward_demodulation,[],[f219,f188])).
% 1.90/0.62  fof(f219,plain,(
% 1.90/0.62    ( ! [X2,X3] : (r1_tarski(k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3)))) )),
% 1.90/0.62    inference(superposition,[],[f80,f134])).
% 1.90/0.62  fof(f80,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f67,f72,f70,f70,f72])).
% 1.90/0.62  fof(f67,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f8])).
% 1.90/0.62  fof(f8,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.90/0.62  fof(f206,plain,(
% 1.90/0.62    spl4_8),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f204])).
% 1.90/0.62  fof(f204,plain,(
% 1.90/0.62    $false | spl4_8),
% 1.90/0.62    inference(resolution,[],[f198,f43])).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    v1_relat_1(sK1)),
% 1.90/0.62    inference(cnf_transformation,[],[f32])).
% 1.90/0.62  fof(f32,plain,(
% 1.90/0.62    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f31,f30])).
% 1.90/0.62  fof(f30,plain,(
% 1.90/0.62    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f22,plain,(
% 1.90/0.62    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,negated_conjecture,(
% 1.90/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.90/0.62    inference(negated_conjecture,[],[f19])).
% 1.90/0.62  fof(f19,conjecture,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 1.90/0.62  fof(f198,plain,(
% 1.90/0.62    ~v1_relat_1(sK1) | spl4_8),
% 1.90/0.62    inference(avatar_component_clause,[],[f196])).
% 1.90/0.62  fof(f196,plain,(
% 1.90/0.62    spl4_8 <=> v1_relat_1(sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.90/0.62  fof(f203,plain,(
% 1.90/0.62    ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_4),
% 1.90/0.62    inference(avatar_split_clause,[],[f184,f160,f200,f196,f166])).
% 1.90/0.62  fof(f166,plain,(
% 1.90/0.62    spl4_5 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.90/0.62  fof(f160,plain,(
% 1.90/0.62    spl4_4 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.90/0.62  fof(f184,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_4),
% 1.90/0.62    inference(resolution,[],[f162,f47])).
% 1.90/0.62  fof(f47,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f23])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,axiom,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.90/0.62  fof(f162,plain,(
% 1.90/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | spl4_4),
% 1.90/0.62    inference(avatar_component_clause,[],[f160])).
% 1.90/0.62  fof(f194,plain,(
% 1.90/0.62    spl4_5),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f193])).
% 1.90/0.62  fof(f193,plain,(
% 1.90/0.62    $false | spl4_5),
% 1.90/0.62    inference(resolution,[],[f190,f76])).
% 1.90/0.62  fof(f76,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f50,f70])).
% 1.90/0.62  fof(f50,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.90/0.62  fof(f190,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl4_5),
% 1.90/0.62    inference(resolution,[],[f189,f42])).
% 1.90/0.62  fof(f42,plain,(
% 1.90/0.62    v1_relat_1(sK0)),
% 1.90/0.62    inference(cnf_transformation,[],[f32])).
% 1.90/0.62  fof(f189,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)) ) | spl4_5),
% 1.90/0.62    inference(resolution,[],[f181,f65])).
% 1.90/0.62  fof(f65,plain,(
% 1.90/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.90/0.62    inference(nnf_transformation,[],[f16])).
% 1.90/0.62  fof(f16,axiom,(
% 1.90/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.90/0.62  fof(f181,plain,(
% 1.90/0.62    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_5),
% 1.90/0.62    inference(resolution,[],[f168,f48])).
% 1.90/0.62  fof(f48,plain,(
% 1.90/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f25])).
% 1.90/0.62  fof(f25,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f17])).
% 1.90/0.62  fof(f17,axiom,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.90/0.62  fof(f168,plain,(
% 1.90/0.62    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_5),
% 1.90/0.62    inference(avatar_component_clause,[],[f166])).
% 1.90/0.62  fof(f183,plain,(
% 1.90/0.62    spl4_7),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f182])).
% 1.90/0.62  fof(f182,plain,(
% 1.90/0.62    $false | spl4_7),
% 1.90/0.62    inference(resolution,[],[f176,f76])).
% 1.90/0.62  fof(f176,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl4_7),
% 1.90/0.62    inference(avatar_component_clause,[],[f174])).
% 1.90/0.62  fof(f174,plain,(
% 1.90/0.62    spl4_7 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.90/0.62  fof(f180,plain,(
% 1.90/0.62    spl4_6),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f178])).
% 1.90/0.62  fof(f178,plain,(
% 1.90/0.62    $false | spl4_6),
% 1.90/0.62    inference(resolution,[],[f172,f42])).
% 1.90/0.62  fof(f172,plain,(
% 1.90/0.62    ~v1_relat_1(sK0) | spl4_6),
% 1.90/0.62    inference(avatar_component_clause,[],[f170])).
% 1.90/0.62  fof(f170,plain,(
% 1.90/0.62    spl4_6 <=> v1_relat_1(sK0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.90/0.62  fof(f177,plain,(
% 1.90/0.62    ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_3),
% 1.90/0.62    inference(avatar_split_clause,[],[f164,f156,f174,f170,f166])).
% 1.90/0.62  fof(f156,plain,(
% 1.90/0.62    spl4_3 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.90/0.62  fof(f164,plain,(
% 1.90/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl4_3),
% 1.90/0.62    inference(resolution,[],[f158,f47])).
% 1.90/0.62  fof(f158,plain,(
% 1.90/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl4_3),
% 1.90/0.62    inference(avatar_component_clause,[],[f156])).
% 1.90/0.62  fof(f163,plain,(
% 1.90/0.62    ~spl4_3 | ~spl4_4),
% 1.90/0.62    inference(avatar_split_clause,[],[f151,f160,f156])).
% 1.90/0.62  fof(f151,plain,(
% 1.90/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.90/0.62    inference(resolution,[],[f81,f73])).
% 1.90/0.62  fof(f73,plain,(
% 1.90/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 1.90/0.62    inference(definition_unfolding,[],[f44,f70,f70])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 1.90/0.62    inference(cnf_transformation,[],[f32])).
% 1.90/0.62  fof(f81,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f68,f70])).
% 1.90/0.62  fof(f68,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f29,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.90/0.62    inference(flattening,[],[f28])).
% 1.90/0.62  fof(f28,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f6])).
% 1.90/0.62  fof(f6,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (5942)------------------------------
% 1.90/0.62  % (5942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (5942)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (5942)Memory used [KB]: 6268
% 1.90/0.62  % (5942)Time elapsed: 0.186 s
% 1.90/0.62  % (5942)------------------------------
% 1.90/0.62  % (5942)------------------------------
% 1.90/0.62  % (5929)Success in time 0.248 s
%------------------------------------------------------------------------------
