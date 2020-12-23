%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 253 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  411 ( 938 expanded)
%              Number of equality atoms :   69 ( 222 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f698,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f117,f299,f678,f683,f697])).

fof(f697,plain,
    ( ~ spl15_1
    | spl15_2
    | ~ spl15_19 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl15_1
    | spl15_2
    | ~ spl15_19 ),
    inference(resolution,[],[f690,f118])).

fof(f118,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f71,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f690,plain,
    ( r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k1_xboole_0)
    | ~ spl15_1
    | spl15_2
    | ~ spl15_19 ),
    inference(forward_demodulation,[],[f689,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl15_1
  <=> k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f689,plain,
    ( r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,sK3))
    | spl15_2
    | ~ spl15_19 ),
    inference(forward_demodulation,[],[f684,f200])).

fof(f200,plain,(
    ! [X0] : k10_relat_1(sK4,X0) = k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),X0))) ),
    inference(resolution,[],[f99,f59])).

fof(f59,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 != k10_relat_1(sK4,sK3) )
    & ( r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 = k10_relat_1(sK4,sK3) )
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 != k10_relat_1(sK4,sK3) )
      & ( r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 = k10_relat_1(sK4,sK3) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f75,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f684,plain,
    ( r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3))))
    | spl15_2
    | ~ spl15_19 ),
    inference(resolution,[],[f677,f321])).

fof(f321,plain,
    ( r2_hidden(sK8(k2_relat_1(sK4),sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)))
    | spl15_2 ),
    inference(resolution,[],[f115,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f115,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl15_2
  <=> r1_xboole_0(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f677,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),X3)
        | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3)) )
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl15_19
  <=> ! [X3] :
        ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),X3)
        | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f683,plain,
    ( spl15_2
    | spl15_18 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | spl15_2
    | spl15_18 ),
    inference(resolution,[],[f674,f416])).

fof(f416,plain,
    ( r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | spl15_2 ),
    inference(resolution,[],[f345,f107])).

fof(f107,plain,(
    ! [X0,X1] : sP2(X1,X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f95,f72])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f345,plain,
    ( ! [X6,X7] :
        ( ~ sP2(X7,X6,k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)))
        | r2_hidden(sK8(k2_relat_1(sK4),sK3),X6) )
    | spl15_2 ),
    inference(resolution,[],[f321,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK14(X0,X1,X2),X0)
              & r2_hidden(sK14(X0,X1,X2),X1) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK14(X0,X1,X2),X0)
            & r2_hidden(sK14(X0,X1,X2),X1) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f674,plain,
    ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | spl15_18 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl15_18
  <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f678,plain,
    ( ~ spl15_18
    | spl15_19
    | spl15_2 ),
    inference(avatar_split_clause,[],[f670,f113,f676,f672])).

fof(f670,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),X3)
        | ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
        | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3)) )
    | spl15_2 ),
    inference(resolution,[],[f576,f417])).

fof(f417,plain,
    ( r2_hidden(k4_tarski(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),sK8(k2_relat_1(sK4),sK3)),sK4)
    | spl15_2 ),
    inference(resolution,[],[f416,f104])).

fof(f104,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

% (6150)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f576,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK4)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(sK4))
      | r2_hidden(X2,k10_relat_1(sK4,X1)) ) ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK13(X0,X1,X2)),X2)
            & r2_hidden(sK13(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK13(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK13(X0,X1,X2)),X2)
        & r2_hidden(sK13(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f299,plain,
    ( spl15_1
    | ~ spl15_2 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl15_1
    | ~ spl15_2 ),
    inference(resolution,[],[f259,f118])).

fof(f259,plain,
    ( r2_hidden(sK13(sK9(k10_relat_1(sK4,k1_xboole_0),k1_xboole_0),k1_xboole_0,sK4),k1_xboole_0)
    | spl15_1
    | ~ spl15_2 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK13(sK9(k10_relat_1(sK4,k1_xboole_0),k1_xboole_0),k1_xboole_0,sK4),k1_xboole_0)
    | spl15_1
    | ~ spl15_2 ),
    inference(superposition,[],[f232,f164])).

fof(f164,plain,(
    ! [X2] :
      ( k1_xboole_0 = k10_relat_1(sK4,X2)
      | r2_hidden(sK13(sK9(k10_relat_1(sK4,X2),k1_xboole_0),X2,sK4),X2) ) ),
    inference(resolution,[],[f162,f134])).

fof(f134,plain,(
    ! [X12] :
      ( r2_hidden(sK9(X12,k1_xboole_0),X12)
      | k1_xboole_0 = X12 ) ),
    inference(resolution,[],[f76,f118])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

% (6138)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
      | r2_hidden(sK13(X0,X1,sK4),X1) ) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK13(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f232,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0)
    | spl15_1
    | ~ spl15_2 ),
    inference(superposition,[],[f111,f216])).

fof(f216,plain,
    ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl15_2 ),
    inference(superposition,[],[f200,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3))
    | ~ spl15_2 ),
    inference(resolution,[],[f142,f114])).

fof(f114,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f142,plain,(
    ! [X10,X9] :
      ( ~ r1_xboole_0(X9,X10)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X9,X10)) ) ),
    inference(resolution,[],[f134,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,sK3)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f117,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f60,f113,f109])).

fof(f60,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,
    ( ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f61,f113,f109])).

fof(f61,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (6151)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.48  % (6135)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (6127)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.57  % (6126)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.74/0.58  % (6134)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.58  % (6142)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.58  % (6125)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.74/0.58  % (6128)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.74/0.59  % (6149)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.74/0.59  % (6122)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.74/0.59  % (6148)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.74/0.59  % (6147)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.74/0.60  % (6124)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.74/0.60  % (6140)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.74/0.60  % (6141)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.74/0.60  % (6129)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.74/0.60  % (6132)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.74/0.60  % (6133)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.74/0.60  % (6139)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.74/0.61  % (6144)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.74/0.61  % (6136)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.74/0.61  % (6145)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.74/0.61  % (6144)Refutation not found, incomplete strategy% (6144)------------------------------
% 1.74/0.61  % (6144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (6143)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.74/0.61  % (6131)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.74/0.61  % (6144)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.61  
% 1.74/0.61  % (6144)Memory used [KB]: 10746
% 1.74/0.61  % (6144)Time elapsed: 0.126 s
% 1.74/0.61  % (6144)------------------------------
% 1.74/0.61  % (6144)------------------------------
% 1.74/0.62  % (6134)Refutation found. Thanks to Tanya!
% 1.74/0.62  % SZS status Theorem for theBenchmark
% 1.74/0.62  % (6123)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.74/0.62  % (6137)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.74/0.63  % SZS output start Proof for theBenchmark
% 1.74/0.63  fof(f698,plain,(
% 1.74/0.63    $false),
% 1.74/0.63    inference(avatar_sat_refutation,[],[f116,f117,f299,f678,f683,f697])).
% 1.74/0.63  fof(f697,plain,(
% 1.74/0.63    ~spl15_1 | spl15_2 | ~spl15_19),
% 1.74/0.63    inference(avatar_contradiction_clause,[],[f692])).
% 1.74/0.63  fof(f692,plain,(
% 1.74/0.63    $false | (~spl15_1 | spl15_2 | ~spl15_19)),
% 1.74/0.63    inference(resolution,[],[f690,f118])).
% 1.74/0.63  fof(f118,plain,(
% 1.74/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.63    inference(superposition,[],[f71,f105])).
% 1.74/0.63  fof(f105,plain,(
% 1.74/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.74/0.63    inference(equality_resolution,[],[f84])).
% 1.74/0.63  fof(f84,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.74/0.63    inference(cnf_transformation,[],[f48])).
% 1.74/0.63  fof(f48,plain,(
% 1.74/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.74/0.63    inference(flattening,[],[f47])).
% 1.74/0.63  fof(f47,plain,(
% 1.74/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.74/0.63    inference(nnf_transformation,[],[f4])).
% 1.74/0.63  fof(f4,axiom,(
% 1.74/0.63    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.74/0.63  fof(f71,plain,(
% 1.74/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f5])).
% 1.74/0.63  fof(f5,axiom,(
% 1.74/0.63    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.74/0.63  fof(f690,plain,(
% 1.74/0.63    r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k1_xboole_0) | (~spl15_1 | spl15_2 | ~spl15_19)),
% 1.74/0.63    inference(forward_demodulation,[],[f689,f110])).
% 1.74/0.63  fof(f110,plain,(
% 1.74/0.63    k1_xboole_0 = k10_relat_1(sK4,sK3) | ~spl15_1),
% 1.74/0.63    inference(avatar_component_clause,[],[f109])).
% 1.74/0.63  fof(f109,plain,(
% 1.74/0.63    spl15_1 <=> k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 1.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 1.74/0.63  fof(f689,plain,(
% 1.74/0.63    r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,sK3)) | (spl15_2 | ~spl15_19)),
% 1.74/0.63    inference(forward_demodulation,[],[f684,f200])).
% 1.74/0.63  fof(f200,plain,(
% 1.74/0.63    ( ! [X0] : (k10_relat_1(sK4,X0) = k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),X0)))) )),
% 1.74/0.63    inference(resolution,[],[f99,f59])).
% 1.74/0.63  fof(f59,plain,(
% 1.74/0.63    v1_relat_1(sK4)),
% 1.74/0.63    inference(cnf_transformation,[],[f28])).
% 1.74/0.63  fof(f28,plain,(
% 1.74/0.63    (~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4)),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).
% 1.74/0.63  fof(f27,plain,(
% 1.74/0.63    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f26,plain,(
% 1.74/0.63    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.74/0.63    inference(flattening,[],[f25])).
% 1.74/0.63  fof(f25,plain,(
% 1.74/0.63    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.74/0.63    inference(nnf_transformation,[],[f14])).
% 1.74/0.63  fof(f14,plain,(
% 1.74/0.63    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.74/0.63    inference(ennf_transformation,[],[f12])).
% 1.74/0.63  fof(f12,negated_conjecture,(
% 1.74/0.63    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.74/0.63    inference(negated_conjecture,[],[f11])).
% 1.74/0.63  fof(f11,conjecture,(
% 1.74/0.63    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.74/0.63  fof(f99,plain,(
% 1.74/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 1.74/0.63    inference(definition_unfolding,[],[f75,f72])).
% 1.74/0.63  fof(f72,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f6])).
% 1.74/0.63  fof(f6,axiom,(
% 1.74/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.74/0.63  fof(f75,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f17])).
% 1.74/0.63  fof(f17,plain,(
% 1.74/0.63    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.74/0.63    inference(ennf_transformation,[],[f10])).
% 1.74/0.63  fof(f10,axiom,(
% 1.74/0.63    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.74/0.63  fof(f684,plain,(
% 1.74/0.63    r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)))) | (spl15_2 | ~spl15_19)),
% 1.74/0.63    inference(resolution,[],[f677,f321])).
% 1.74/0.63  fof(f321,plain,(
% 1.74/0.63    r2_hidden(sK8(k2_relat_1(sK4),sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3))) | spl15_2),
% 1.74/0.63    inference(resolution,[],[f115,f98])).
% 1.74/0.63  fof(f98,plain,(
% 1.74/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK8(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.74/0.63    inference(definition_unfolding,[],[f73,f72])).
% 1.74/0.63  fof(f73,plain,(
% 1.74/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f37])).
% 1.74/0.63  fof(f37,plain,(
% 1.74/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f36])).
% 1.74/0.63  fof(f36,plain,(
% 1.74/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f16,plain,(
% 1.74/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.74/0.63    inference(ennf_transformation,[],[f13])).
% 1.74/0.63  fof(f13,plain,(
% 1.74/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.63    inference(rectify,[],[f3])).
% 1.74/0.63  fof(f3,axiom,(
% 1.74/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.74/0.63  fof(f115,plain,(
% 1.74/0.63    ~r1_xboole_0(k2_relat_1(sK4),sK3) | spl15_2),
% 1.74/0.63    inference(avatar_component_clause,[],[f113])).
% 1.74/0.63  fof(f113,plain,(
% 1.74/0.63    spl15_2 <=> r1_xboole_0(k2_relat_1(sK4),sK3)),
% 1.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 1.74/0.63  fof(f677,plain,(
% 1.74/0.63    ( ! [X3] : (~r2_hidden(sK8(k2_relat_1(sK4),sK3),X3) | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3))) ) | ~spl15_19),
% 1.74/0.63    inference(avatar_component_clause,[],[f676])).
% 1.74/0.63  fof(f676,plain,(
% 1.74/0.63    spl15_19 <=> ! [X3] : (~r2_hidden(sK8(k2_relat_1(sK4),sK3),X3) | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3)))),
% 1.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).
% 1.74/0.63  fof(f683,plain,(
% 1.74/0.63    spl15_2 | spl15_18),
% 1.74/0.63    inference(avatar_contradiction_clause,[],[f681])).
% 1.74/0.63  fof(f681,plain,(
% 1.74/0.63    $false | (spl15_2 | spl15_18)),
% 1.74/0.63    inference(resolution,[],[f674,f416])).
% 1.74/0.63  fof(f416,plain,(
% 1.74/0.63    r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | spl15_2),
% 1.74/0.63    inference(resolution,[],[f345,f107])).
% 1.74/0.63  fof(f107,plain,(
% 1.74/0.63    ( ! [X0,X1] : (sP2(X1,X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.74/0.63    inference(equality_resolution,[],[f101])).
% 1.74/0.63  fof(f101,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.74/0.63    inference(definition_unfolding,[],[f95,f72])).
% 1.74/0.63  fof(f95,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.74/0.63    inference(cnf_transformation,[],[f58])).
% 1.74/0.63  fof(f58,plain,(
% 1.74/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.74/0.63    inference(nnf_transformation,[],[f24])).
% 1.74/0.63  fof(f24,plain,(
% 1.74/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.74/0.63    inference(definition_folding,[],[f1,f23])).
% 1.74/0.63  fof(f23,plain,(
% 1.74/0.63    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.74/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.74/0.63  fof(f1,axiom,(
% 1.74/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.74/0.63  fof(f345,plain,(
% 1.74/0.63    ( ! [X6,X7] : (~sP2(X7,X6,k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3))) | r2_hidden(sK8(k2_relat_1(sK4),sK3),X6)) ) | spl15_2),
% 1.74/0.63    inference(resolution,[],[f321,f89])).
% 1.74/0.63  fof(f89,plain,(
% 1.74/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP2(X0,X1,X2)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f57])).
% 1.74/0.63  fof(f57,plain,(
% 1.74/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((r2_hidden(sK14(X0,X1,X2),X0) & r2_hidden(sK14(X0,X1,X2),X1)) | r2_hidden(sK14(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f55,f56])).
% 1.74/0.63  fof(f56,plain,(
% 1.74/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((r2_hidden(sK14(X0,X1,X2),X0) & r2_hidden(sK14(X0,X1,X2),X1)) | r2_hidden(sK14(X0,X1,X2),X2))))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f55,plain,(
% 1.74/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.74/0.63    inference(rectify,[],[f54])).
% 1.74/0.63  fof(f54,plain,(
% 1.74/0.63    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.74/0.63    inference(flattening,[],[f53])).
% 1.74/0.63  fof(f53,plain,(
% 1.74/0.63    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.74/0.63    inference(nnf_transformation,[],[f23])).
% 1.74/0.63  fof(f674,plain,(
% 1.74/0.63    ~r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | spl15_18),
% 1.74/0.63    inference(avatar_component_clause,[],[f672])).
% 1.74/0.63  fof(f672,plain,(
% 1.74/0.63    spl15_18 <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))),
% 1.74/0.63    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).
% 1.74/0.63  fof(f678,plain,(
% 1.74/0.63    ~spl15_18 | spl15_19 | spl15_2),
% 1.74/0.63    inference(avatar_split_clause,[],[f670,f113,f676,f672])).
% 1.74/0.63  fof(f670,plain,(
% 1.74/0.63    ( ! [X3] : (~r2_hidden(sK8(k2_relat_1(sK4),sK3),X3) | ~r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | r2_hidden(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),k10_relat_1(sK4,X3))) ) | spl15_2),
% 1.74/0.63    inference(resolution,[],[f576,f417])).
% 1.74/0.63  fof(f417,plain,(
% 1.74/0.63    r2_hidden(k4_tarski(sK12(sK4,sK8(k2_relat_1(sK4),sK3)),sK8(k2_relat_1(sK4),sK3)),sK4) | spl15_2),
% 1.74/0.63    inference(resolution,[],[f416,f104])).
% 1.74/0.63  fof(f104,plain,(
% 1.74/0.63    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)) )),
% 1.74/0.63    inference(equality_resolution,[],[f78])).
% 1.74/0.63  fof(f78,plain,(
% 1.74/0.63    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.74/0.63    inference(cnf_transformation,[],[f46])).
% 1.74/0.63  fof(f46,plain,(
% 1.74/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f42,f45,f44,f43])).
% 1.74/0.63  fof(f43,plain,(
% 1.74/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f44,plain,(
% 1.74/0.63    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0) => r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f45,plain,(
% 1.74/0.63    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f42,plain,(
% 1.74/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.74/0.63    inference(rectify,[],[f41])).
% 1.74/0.63  fof(f41,plain,(
% 1.74/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.74/0.63    inference(nnf_transformation,[],[f8])).
% 1.74/0.63  fof(f8,axiom,(
% 1.74/0.63    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.74/0.63  % (6150)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.74/0.63  fof(f576,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK4) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(sK4)) | r2_hidden(X2,k10_relat_1(sK4,X1))) )),
% 1.74/0.63    inference(resolution,[],[f88,f59])).
% 1.74/0.63  fof(f88,plain,(
% 1.74/0.63    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f52])).
% 1.74/0.63  fof(f52,plain,(
% 1.74/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK13(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK13(X0,X1,X2)),X2) & r2_hidden(sK13(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f50,f51])).
% 1.74/0.63  fof(f51,plain,(
% 1.74/0.63    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK13(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK13(X0,X1,X2)),X2) & r2_hidden(sK13(X0,X1,X2),k2_relat_1(X2))))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f50,plain,(
% 1.74/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.74/0.63    inference(rectify,[],[f49])).
% 1.74/0.63  fof(f49,plain,(
% 1.74/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.74/0.63    inference(nnf_transformation,[],[f19])).
% 1.74/0.63  fof(f19,plain,(
% 1.74/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.74/0.63    inference(ennf_transformation,[],[f9])).
% 1.74/0.63  fof(f9,axiom,(
% 1.74/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.74/0.63  fof(f299,plain,(
% 1.74/0.63    spl15_1 | ~spl15_2),
% 1.74/0.63    inference(avatar_contradiction_clause,[],[f294])).
% 1.74/0.63  fof(f294,plain,(
% 1.74/0.63    $false | (spl15_1 | ~spl15_2)),
% 1.74/0.63    inference(resolution,[],[f259,f118])).
% 1.74/0.63  fof(f259,plain,(
% 1.74/0.63    r2_hidden(sK13(sK9(k10_relat_1(sK4,k1_xboole_0),k1_xboole_0),k1_xboole_0,sK4),k1_xboole_0) | (spl15_1 | ~spl15_2)),
% 1.74/0.63    inference(trivial_inequality_removal,[],[f258])).
% 1.74/0.63  fof(f258,plain,(
% 1.74/0.63    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK13(sK9(k10_relat_1(sK4,k1_xboole_0),k1_xboole_0),k1_xboole_0,sK4),k1_xboole_0) | (spl15_1 | ~spl15_2)),
% 1.74/0.63    inference(superposition,[],[f232,f164])).
% 1.74/0.63  fof(f164,plain,(
% 1.74/0.63    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK4,X2) | r2_hidden(sK13(sK9(k10_relat_1(sK4,X2),k1_xboole_0),X2,sK4),X2)) )),
% 1.74/0.63    inference(resolution,[],[f162,f134])).
% 1.74/0.63  fof(f134,plain,(
% 1.74/0.63    ( ! [X12] : (r2_hidden(sK9(X12,k1_xboole_0),X12) | k1_xboole_0 = X12) )),
% 1.74/0.63    inference(resolution,[],[f76,f118])).
% 1.74/0.63  fof(f76,plain,(
% 1.74/0.63    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | X0 = X1 | r2_hidden(sK9(X0,X1),X0)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f40])).
% 1.74/0.63  % (6138)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.74/0.63  fof(f40,plain,(
% 1.74/0.63    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 1.74/0.63  fof(f39,plain,(
% 1.74/0.63    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.63  fof(f38,plain,(
% 1.74/0.63    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.74/0.63    inference(nnf_transformation,[],[f18])).
% 1.74/0.63  fof(f18,plain,(
% 1.74/0.63    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.74/0.63    inference(ennf_transformation,[],[f2])).
% 1.74/0.63  fof(f2,axiom,(
% 1.74/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.74/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.74/0.63  fof(f162,plain,(
% 1.74/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK4,X1)) | r2_hidden(sK13(X0,X1,sK4),X1)) )),
% 1.74/0.63    inference(resolution,[],[f87,f59])).
% 1.74/0.63  fof(f87,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK13(X0,X1,X2),X1)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f52])).
% 1.74/0.63  fof(f232,plain,(
% 1.74/0.63    k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) | (spl15_1 | ~spl15_2)),
% 1.74/0.63    inference(superposition,[],[f111,f216])).
% 1.74/0.63  fof(f216,plain,(
% 1.74/0.63    k10_relat_1(sK4,sK3) = k10_relat_1(sK4,k1_xboole_0) | ~spl15_2),
% 1.74/0.63    inference(superposition,[],[f200,f153])).
% 1.74/0.63  fof(f153,plain,(
% 1.74/0.63    k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)) | ~spl15_2),
% 1.74/0.63    inference(resolution,[],[f142,f114])).
% 1.74/0.63  fof(f114,plain,(
% 1.74/0.63    r1_xboole_0(k2_relat_1(sK4),sK3) | ~spl15_2),
% 1.74/0.63    inference(avatar_component_clause,[],[f113])).
% 1.74/0.63  fof(f142,plain,(
% 1.74/0.63    ( ! [X10,X9] : (~r1_xboole_0(X9,X10) | k1_xboole_0 = k1_setfam_1(k2_tarski(X9,X10))) )),
% 1.74/0.63    inference(resolution,[],[f134,f97])).
% 1.74/0.63  fof(f97,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.74/0.63    inference(definition_unfolding,[],[f74,f72])).
% 1.74/0.63  fof(f74,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f37])).
% 1.74/0.63  fof(f111,plain,(
% 1.74/0.63    k1_xboole_0 != k10_relat_1(sK4,sK3) | spl15_1),
% 1.74/0.63    inference(avatar_component_clause,[],[f109])).
% 1.74/0.63  fof(f117,plain,(
% 1.74/0.63    spl15_1 | spl15_2),
% 1.74/0.63    inference(avatar_split_clause,[],[f60,f113,f109])).
% 1.74/0.63  fof(f60,plain,(
% 1.74/0.63    r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 1.74/0.63    inference(cnf_transformation,[],[f28])).
% 1.74/0.63  fof(f116,plain,(
% 1.74/0.63    ~spl15_1 | ~spl15_2),
% 1.74/0.63    inference(avatar_split_clause,[],[f61,f113,f109])).
% 1.74/0.63  fof(f61,plain,(
% 1.74/0.63    ~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)),
% 1.74/0.63    inference(cnf_transformation,[],[f28])).
% 1.74/0.63  % SZS output end Proof for theBenchmark
% 1.74/0.63  % (6134)------------------------------
% 1.74/0.63  % (6134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.63  % (6134)Termination reason: Refutation
% 1.74/0.63  
% 1.74/0.63  % (6134)Memory used [KB]: 6780
% 1.74/0.63  % (6134)Time elapsed: 0.173 s
% 1.74/0.63  % (6134)------------------------------
% 1.74/0.63  % (6134)------------------------------
% 1.74/0.63  % (6121)Success in time 0.274 s
%------------------------------------------------------------------------------
