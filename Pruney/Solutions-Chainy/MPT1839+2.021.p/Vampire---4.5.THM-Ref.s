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
% DateTime   : Thu Dec  3 13:20:04 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 232 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  276 ( 591 expanded)
%              Number of equality atoms :   47 ( 139 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f126,f131,f147,f160,f323,f324])).

fof(f324,plain,
    ( sK0 != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f323,plain,
    ( ~ spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f312,f128,f320])).

fof(f320,plain,
    ( spl4_16
  <=> r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f128,plain,
    ( spl4_6
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f312,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f148,f77])).

fof(f77,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f148,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,sK1),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0))))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f130,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f130,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f160,plain,
    ( spl4_8
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f149,f128,f123,f157])).

fof(f157,plain,
    ( spl4_8
  <=> r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( spl4_5
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f149,plain,
    ( r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f125,f130,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f147,plain,
    ( spl4_7
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f140,f107,f102,f97,f144])).

fof(f144,plain,
    ( spl4_7
  <=> sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f97,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( spl4_3
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f107,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f140,plain,
    ( sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f104,f109,f79,f99,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f99,plain,
    ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f109,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f104,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f131,plain,
    ( spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f118,f92,f128])).

fof(f92,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f118,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f94,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f94,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f126,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f119,f92,f123])).

fof(f119,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f39,f107])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f105,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f75,f97])).

fof(f75,plain,(
    ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f41,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.32/0.53  % (30101)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (30100)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.54  % (30101)Refutation not found, incomplete strategy% (30101)------------------------------
% 1.32/0.54  % (30101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (30101)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (30090)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (30101)Memory used [KB]: 10618
% 1.32/0.54  % (30101)Time elapsed: 0.127 s
% 1.32/0.54  % (30101)------------------------------
% 1.32/0.54  % (30101)------------------------------
% 1.32/0.54  % (30090)Refutation not found, incomplete strategy% (30090)------------------------------
% 1.32/0.54  % (30090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (30090)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (30090)Memory used [KB]: 1663
% 1.32/0.54  % (30090)Time elapsed: 0.122 s
% 1.32/0.54  % (30090)------------------------------
% 1.32/0.54  % (30090)------------------------------
% 1.32/0.54  % (30105)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (30100)Refutation not found, incomplete strategy% (30100)------------------------------
% 1.32/0.54  % (30100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (30100)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (30100)Memory used [KB]: 10618
% 1.32/0.54  % (30100)Time elapsed: 0.110 s
% 1.32/0.54  % (30100)------------------------------
% 1.32/0.54  % (30100)------------------------------
% 1.32/0.54  % (30115)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (30093)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.55  % (30118)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (30107)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.55  % (30107)Refutation not found, incomplete strategy% (30107)------------------------------
% 1.32/0.55  % (30107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (30107)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (30107)Memory used [KB]: 10618
% 1.32/0.55  % (30107)Time elapsed: 0.146 s
% 1.32/0.55  % (30107)------------------------------
% 1.32/0.55  % (30107)------------------------------
% 1.32/0.55  % (30113)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.55  % (30110)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.55/0.55  % (30097)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.56  % (30110)Refutation not found, incomplete strategy% (30110)------------------------------
% 1.55/0.56  % (30110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (30110)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (30110)Memory used [KB]: 10746
% 1.55/0.56  % (30110)Time elapsed: 0.127 s
% 1.55/0.56  % (30110)------------------------------
% 1.55/0.56  % (30110)------------------------------
% 1.55/0.56  % (30091)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.55/0.56  % (30094)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.57  % (30119)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.55/0.57  % (30102)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (30095)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.57  % (30116)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.57  % (30115)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f325,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f126,f131,f147,f160,f323,f324])).
% 1.55/0.57  fof(f324,plain,(
% 1.55/0.57    sK0 != k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0))),
% 1.55/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.55/0.57  fof(f323,plain,(
% 1.55/0.57    ~spl4_16 | ~spl4_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f312,f128,f320])).
% 1.55/0.57  fof(f320,plain,(
% 1.55/0.57    spl4_16 <=> r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.55/0.57  fof(f128,plain,(
% 1.55/0.57    spl4_6 <=> r2_hidden(sK2(sK0,sK1),sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.55/0.57  fof(f312,plain,(
% 1.55/0.57    ~r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,sK0)) | ~spl4_6),
% 1.55/0.57    inference(superposition,[],[f148,f77])).
% 1.55/0.57  fof(f77,plain,(
% 1.55/0.57    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.55/0.57    inference(definition_unfolding,[],[f45,f73])).
% 1.55/0.57  fof(f73,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.55/0.57    inference(definition_unfolding,[],[f48,f72])).
% 1.55/0.57  fof(f72,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f49,f71])).
% 1.55/0.57  fof(f71,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f57,f70])).
% 1.55/0.57  fof(f70,plain,(
% 1.55/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f64,f69])).
% 1.55/0.57  fof(f69,plain,(
% 1.55/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f65,f68])).
% 1.55/0.57  fof(f68,plain,(
% 1.55/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f66,f67])).
% 1.55/0.58  fof(f67,plain,(
% 1.55/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f14])).
% 1.55/0.58  fof(f14,axiom,(
% 1.55/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.55/0.58  fof(f66,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f13])).
% 1.55/0.58  fof(f13,axiom,(
% 1.55/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f12])).
% 1.55/0.58  fof(f12,axiom,(
% 1.55/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.55/0.58  fof(f64,plain,(
% 1.55/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f11])).
% 1.55/0.58  fof(f11,axiom,(
% 1.55/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.55/0.58  fof(f57,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f10])).
% 1.55/0.58  fof(f10,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f9])).
% 1.55/0.58  fof(f9,axiom,(
% 1.55/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.58  fof(f48,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,axiom,(
% 1.55/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.55/0.58  fof(f45,plain,(
% 1.55/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.58    inference(rectify,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.55/0.58  fof(f148,plain,(
% 1.55/0.58    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0))))) ) | ~spl4_6),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f130,f89])).
% 1.55/0.58  fof(f89,plain,(
% 1.55/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.55/0.58    inference(equality_resolution,[],[f84])).
% 1.55/0.58  fof(f84,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 1.55/0.58    inference(definition_unfolding,[],[f59,f74])).
% 1.55/0.58  fof(f74,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.55/0.58    inference(definition_unfolding,[],[f50,f73])).
% 1.55/0.58  fof(f50,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.58  fof(f59,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f38])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.58    inference(rectify,[],[f35])).
% 1.55/0.58  fof(f35,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.58    inference(flattening,[],[f34])).
% 1.55/0.58  fof(f34,plain,(
% 1.55/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.55/0.58    inference(nnf_transformation,[],[f2])).
% 1.55/0.58  fof(f2,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.55/0.58  fof(f130,plain,(
% 1.55/0.58    r2_hidden(sK2(sK0,sK1),sK0) | ~spl4_6),
% 1.55/0.58    inference(avatar_component_clause,[],[f128])).
% 1.55/0.58  fof(f160,plain,(
% 1.55/0.58    spl4_8 | spl4_5 | ~spl4_6),
% 1.55/0.58    inference(avatar_split_clause,[],[f149,f128,f123,f157])).
% 1.55/0.58  fof(f157,plain,(
% 1.55/0.58    spl4_8 <=> r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.55/0.58  fof(f123,plain,(
% 1.55/0.58    spl4_5 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.55/0.58  fof(f149,plain,(
% 1.55/0.58    r2_hidden(sK2(sK0,sK1),k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_5 | ~spl4_6)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f125,f130,f88])).
% 1.55/0.58  fof(f88,plain,(
% 1.55/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.55/0.58    inference(equality_resolution,[],[f83])).
% 1.55/0.58  fof(f83,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 1.55/0.58    inference(definition_unfolding,[],[f60,f74])).
% 1.55/0.58  fof(f60,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f38])).
% 1.55/0.58  fof(f125,plain,(
% 1.55/0.58    ~r2_hidden(sK2(sK0,sK1),sK1) | spl4_5),
% 1.55/0.58    inference(avatar_component_clause,[],[f123])).
% 1.55/0.58  fof(f147,plain,(
% 1.55/0.58    spl4_7 | spl4_2 | ~spl4_3 | spl4_4),
% 1.55/0.58    inference(avatar_split_clause,[],[f140,f107,f102,f97,f144])).
% 1.55/0.58  fof(f144,plain,(
% 1.55/0.58    spl4_7 <=> sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.55/0.58  fof(f97,plain,(
% 1.55/0.58    spl4_2 <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.55/0.58  fof(f102,plain,(
% 1.55/0.58    spl4_3 <=> v1_zfmisc_1(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.55/0.58  fof(f107,plain,(
% 1.55/0.58    spl4_4 <=> v1_xboole_0(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.55/0.58  fof(f140,plain,(
% 1.55/0.58    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f104,f109,f79,f99,f44])).
% 1.55/0.58  fof(f44,plain,(
% 1.55/0.58    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f23])).
% 1.55/0.58  fof(f23,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.55/0.58    inference(flattening,[],[f22])).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f16])).
% 1.55/0.58  fof(f16,axiom,(
% 1.55/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.55/0.58  fof(f99,plain,(
% 1.55/0.58    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl4_2),
% 1.55/0.58    inference(avatar_component_clause,[],[f97])).
% 1.55/0.58  fof(f79,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.55/0.58    inference(definition_unfolding,[],[f47,f73])).
% 1.55/0.58  fof(f47,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f6])).
% 1.55/0.58  fof(f6,axiom,(
% 1.55/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.55/0.58  fof(f109,plain,(
% 1.55/0.58    ~v1_xboole_0(sK0) | spl4_4),
% 1.55/0.58    inference(avatar_component_clause,[],[f107])).
% 1.55/0.58  fof(f104,plain,(
% 1.55/0.58    v1_zfmisc_1(sK0) | ~spl4_3),
% 1.55/0.58    inference(avatar_component_clause,[],[f102])).
% 1.55/0.58  fof(f131,plain,(
% 1.55/0.58    spl4_6 | spl4_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f118,f92,f128])).
% 1.55/0.58  fof(f92,plain,(
% 1.55/0.58    spl4_1 <=> r1_tarski(sK0,sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.55/0.58  fof(f118,plain,(
% 1.55/0.58    r2_hidden(sK2(sK0,sK1),sK0) | spl4_1),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f94,f55])).
% 1.55/0.58  fof(f55,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f33])).
% 1.55/0.58  fof(f33,plain,(
% 1.55/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.55/0.58  fof(f32,plain,(
% 1.55/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.58    inference(rectify,[],[f30])).
% 1.55/0.58  fof(f30,plain,(
% 1.55/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.58    inference(nnf_transformation,[],[f24])).
% 1.55/0.58  fof(f24,plain,(
% 1.55/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.58  fof(f94,plain,(
% 1.55/0.58    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.55/0.58    inference(avatar_component_clause,[],[f92])).
% 1.55/0.58  fof(f126,plain,(
% 1.55/0.58    ~spl4_5 | spl4_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f119,f92,f123])).
% 1.55/0.58  fof(f119,plain,(
% 1.55/0.58    ~r2_hidden(sK2(sK0,sK1),sK1) | spl4_1),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f94,f56])).
% 1.55/0.58  fof(f56,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f33])).
% 1.55/0.58  fof(f110,plain,(
% 1.55/0.58    ~spl4_4),
% 1.55/0.58    inference(avatar_split_clause,[],[f39,f107])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    ~v1_xboole_0(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  fof(f27,plain,(
% 1.55/0.58    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26,f25])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f21,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.55/0.58    inference(flattening,[],[f20])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f18])).
% 1.55/0.58  fof(f18,negated_conjecture,(
% 1.55/0.58    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.55/0.58    inference(negated_conjecture,[],[f17])).
% 1.55/0.58  fof(f17,conjecture,(
% 1.55/0.58    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 1.55/0.58  fof(f105,plain,(
% 1.55/0.58    spl4_3),
% 1.55/0.58    inference(avatar_split_clause,[],[f40,f102])).
% 1.55/0.58  fof(f40,plain,(
% 1.55/0.58    v1_zfmisc_1(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  fof(f100,plain,(
% 1.55/0.58    ~spl4_2),
% 1.55/0.58    inference(avatar_split_clause,[],[f75,f97])).
% 1.55/0.58  fof(f75,plain,(
% 1.55/0.58    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.55/0.58    inference(definition_unfolding,[],[f41,f73])).
% 1.55/0.58  fof(f41,plain,(
% 1.55/0.58    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  fof(f95,plain,(
% 1.55/0.58    ~spl4_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f42,f92])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    ~r1_tarski(sK0,sK1)),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (30115)------------------------------
% 1.55/0.58  % (30115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (30115)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (30115)Memory used [KB]: 6396
% 1.55/0.58  % (30115)Time elapsed: 0.169 s
% 1.55/0.58  % (30115)------------------------------
% 1.55/0.58  % (30115)------------------------------
% 1.55/0.58  % (30089)Success in time 0.212 s
%------------------------------------------------------------------------------
