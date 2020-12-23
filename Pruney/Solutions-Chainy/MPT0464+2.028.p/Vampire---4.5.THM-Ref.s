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
% DateTime   : Thu Dec  3 12:47:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 317 expanded)
%              Number of leaves         :   26 ( 119 expanded)
%              Depth                    :   10
%              Number of atoms          :  204 ( 561 expanded)
%              Number of equality atoms :   23 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f92,f94,f96,f101,f106,f131,f133,f140])).

fof(f140,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f130,f108])).

% (1935)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f108,plain,(
    ! [X2,X0] : r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X0)),X0) ),
    inference(superposition,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f39,f51,f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f103,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(definition_unfolding,[],[f44,f49,f51,f51,f49,f49])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f43,f51,f49,f49,f51])).

fof(f43,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f130,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_10
  <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f133,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f126,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f126,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f131,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | ~ spl3_5
    | ~ spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f122,f71,f128,f85,f124,f77])).

fof(f77,plain,
    ( spl3_3
  <=> v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f71,plain,
    ( spl3_2
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f122,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_2 ),
    inference(resolution,[],[f73,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f73,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f106,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f91,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_6
  <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f101,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f97,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f79,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f96,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f87,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f94,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f83,f29])).

fof(f83,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f75,f67,f89,f85,f81,f77])).

fof(f67,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_1 ),
    inference(resolution,[],[f69,f32])).

fof(f69,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f71,f67])).

fof(f65,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f31,f49,f49])).

fof(f31,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (1928)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1930)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (1926)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (1929)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (1927)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1932)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (1936)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (1934)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (1938)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (1937)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (1928)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f74,f92,f94,f96,f101,f106,f131,f133,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    $false | spl3_10),
% 0.21/0.48    inference(resolution,[],[f130,f108])).
% 0.21/0.48  % (1935)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X0)),X0)) )),
% 0.21/0.48    inference(superposition,[],[f103,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f51,f49,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f49])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f35,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f37,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f42,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f36,f48])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f55,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f44,f49,f51,f51,f49,f49])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f51,f49,f49,f51])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) | spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_10 <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    $false | spl3_9),
% 0.21/0.48    inference(resolution,[],[f126,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_9 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_9 | ~spl3_5 | ~spl3_10 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f71,f128,f85,f124,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_3 <=> v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_5 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_2),
% 0.21/0.49    inference(resolution,[],[f73,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    $false | spl3_6),
% 0.21/0.49    inference(resolution,[],[f91,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f49])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_6 <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    $false | spl3_3),
% 0.21/0.49    inference(resolution,[],[f97,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.49    inference(resolution,[],[f79,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f53,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f33,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    $false | spl3_5),
% 0.21/0.49    inference(resolution,[],[f87,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    $false | spl3_4),
% 0.21/0.49    inference(resolution,[],[f83,f29])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_4 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f67,f89,f85,f81,f77])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f69,f32])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f71,f67])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f52,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f45,f49])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.21/0.49    inference(definition_unfolding,[],[f31,f49,f49])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1928)------------------------------
% 0.21/0.49  % (1928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1928)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1928)Memory used [KB]: 6140
% 0.21/0.49  % (1928)Time elapsed: 0.060 s
% 0.21/0.49  % (1928)------------------------------
% 0.21/0.49  % (1928)------------------------------
% 0.21/0.49  % (1923)Success in time 0.126 s
%------------------------------------------------------------------------------
