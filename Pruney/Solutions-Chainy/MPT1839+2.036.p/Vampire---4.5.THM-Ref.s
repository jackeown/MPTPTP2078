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
% DateTime   : Thu Dec  3 13:20:06 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 236 expanded)
%              Number of leaves         :   26 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  283 ( 604 expanded)
%              Number of equality atoms :   47 ( 141 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f120,f125,f144,f262,f343])).

fof(f343,plain,
    ( ~ spl5_14
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f339,f122,f257])).

fof(f257,plain,
    ( spl5_14
  <=> r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f122,plain,
    ( spl5_6
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f339,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0))
    | ~ spl5_6 ),
    inference(superposition,[],[f145,f78])).

fof(f78,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,sK1),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0))))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f124,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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

fof(f124,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f262,plain,
    ( spl5_14
    | spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f261,f141,f122,f117,f257])).

fof(f117,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f141,plain,
    ( spl5_8
  <=> sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f261,plain,
    ( r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0))
    | spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f250,f119])).

fof(f119,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f250,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0))
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(resolution,[],[f175,f124])).

fof(f175,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | r2_hidden(X3,sK1)
        | r2_hidden(X3,k5_xboole_0(sK0,sK0)) )
    | ~ spl5_8 ),
    inference(superposition,[],[f86,f143])).

fof(f143,plain,
    ( sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f86,plain,(
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
    inference(definition_unfolding,[],[f61,f75])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f144,plain,
    ( spl5_8
    | spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f137,f105,f100,f95,f141])).

fof(f95,plain,
    ( spl5_2
  <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( spl5_3
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f105,plain,
    ( spl5_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f137,plain,
    ( sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f102,f107,f79,f97,f47])).

fof(f47,plain,(
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

fof(f97,plain,
    ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f107,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f102,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f125,plain,
    ( spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f112,f90,f122])).

fof(f90,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f112,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f92,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f120,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f113,f90,f117])).

fof(f113,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f41,f105])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f103,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f76,f95])).

fof(f76,plain,(
    ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.35  ipcrm: permission denied for id (819593217)
% 0.13/0.36  ipcrm: permission denied for id (823296002)
% 0.13/0.36  ipcrm: permission denied for id (823328771)
% 0.13/0.36  ipcrm: permission denied for id (819691524)
% 0.13/0.36  ipcrm: permission denied for id (819789830)
% 0.13/0.36  ipcrm: permission denied for id (819822599)
% 0.13/0.36  ipcrm: permission denied for id (823394312)
% 0.13/0.36  ipcrm: permission denied for id (823427081)
% 0.13/0.36  ipcrm: permission denied for id (819920906)
% 0.13/0.37  ipcrm: permission denied for id (823525389)
% 0.13/0.37  ipcrm: permission denied for id (820051984)
% 0.13/0.37  ipcrm: permission denied for id (823623697)
% 0.13/0.37  ipcrm: permission denied for id (823656466)
% 0.13/0.38  ipcrm: permission denied for id (823689235)
% 0.13/0.38  ipcrm: permission denied for id (823722004)
% 0.13/0.38  ipcrm: permission denied for id (820183061)
% 0.13/0.38  ipcrm: permission denied for id (823787543)
% 0.13/0.38  ipcrm: permission denied for id (820281369)
% 0.13/0.38  ipcrm: permission denied for id (820314138)
% 0.13/0.38  ipcrm: permission denied for id (820346907)
% 0.13/0.39  ipcrm: permission denied for id (820379676)
% 0.13/0.39  ipcrm: permission denied for id (823853085)
% 0.13/0.39  ipcrm: permission denied for id (820445215)
% 0.13/0.39  ipcrm: permission denied for id (823951393)
% 0.13/0.39  ipcrm: permission denied for id (823984162)
% 0.13/0.39  ipcrm: permission denied for id (824016931)
% 0.13/0.40  ipcrm: permission denied for id (820707368)
% 0.13/0.40  ipcrm: permission denied for id (824180777)
% 0.13/0.40  ipcrm: permission denied for id (824246315)
% 0.13/0.41  ipcrm: permission denied for id (820871213)
% 0.13/0.41  ipcrm: permission denied for id (820903982)
% 0.13/0.41  ipcrm: permission denied for id (824311855)
% 0.13/0.41  ipcrm: permission denied for id (820969520)
% 0.13/0.41  ipcrm: permission denied for id (821002289)
% 0.13/0.41  ipcrm: permission denied for id (821067827)
% 0.13/0.41  ipcrm: permission denied for id (824442932)
% 0.13/0.42  ipcrm: permission denied for id (821133365)
% 0.13/0.42  ipcrm: permission denied for id (821198903)
% 0.13/0.42  ipcrm: permission denied for id (821264441)
% 0.13/0.42  ipcrm: permission denied for id (824541243)
% 0.20/0.42  ipcrm: permission denied for id (821329981)
% 0.20/0.43  ipcrm: permission denied for id (821395519)
% 0.20/0.43  ipcrm: permission denied for id (821428289)
% 0.20/0.43  ipcrm: permission denied for id (824672322)
% 0.20/0.43  ipcrm: permission denied for id (821493827)
% 0.20/0.43  ipcrm: permission denied for id (821526597)
% 0.20/0.44  ipcrm: permission denied for id (821559366)
% 0.20/0.44  ipcrm: permission denied for id (821592135)
% 0.20/0.44  ipcrm: permission denied for id (821657673)
% 0.20/0.44  ipcrm: permission denied for id (821690442)
% 0.20/0.44  ipcrm: permission denied for id (821723211)
% 0.20/0.44  ipcrm: permission denied for id (821788750)
% 0.20/0.45  ipcrm: permission denied for id (824836175)
% 0.20/0.45  ipcrm: permission denied for id (821854288)
% 0.20/0.45  ipcrm: permission denied for id (824934483)
% 0.20/0.45  ipcrm: permission denied for id (821985364)
% 0.20/0.45  ipcrm: permission denied for id (822018133)
% 0.20/0.45  ipcrm: permission denied for id (824967254)
% 0.20/0.46  ipcrm: permission denied for id (822083671)
% 0.20/0.46  ipcrm: permission denied for id (822116440)
% 0.20/0.46  ipcrm: permission denied for id (822149209)
% 0.20/0.46  ipcrm: permission denied for id (822181978)
% 0.20/0.46  ipcrm: permission denied for id (825000027)
% 0.20/0.46  ipcrm: permission denied for id (825032796)
% 0.20/0.46  ipcrm: permission denied for id (825065565)
% 0.20/0.46  ipcrm: permission denied for id (822280286)
% 0.20/0.47  ipcrm: permission denied for id (825098335)
% 0.20/0.47  ipcrm: permission denied for id (822345824)
% 0.20/0.47  ipcrm: permission denied for id (822411362)
% 0.20/0.47  ipcrm: permission denied for id (825163875)
% 0.20/0.47  ipcrm: permission denied for id (822476902)
% 0.20/0.47  ipcrm: permission denied for id (822509671)
% 0.20/0.48  ipcrm: permission denied for id (822607979)
% 0.20/0.48  ipcrm: permission denied for id (825360492)
% 0.20/0.48  ipcrm: permission denied for id (822673517)
% 0.20/0.48  ipcrm: permission denied for id (822706286)
% 0.20/0.48  ipcrm: permission denied for id (825393263)
% 0.20/0.49  ipcrm: permission denied for id (822771824)
% 0.20/0.49  ipcrm: permission denied for id (822870131)
% 0.20/0.49  ipcrm: permission denied for id (825491572)
% 0.20/0.49  ipcrm: permission denied for id (822968437)
% 0.20/0.49  ipcrm: permission denied for id (823033975)
% 0.20/0.50  ipcrm: permission denied for id (823099513)
% 0.20/0.50  ipcrm: permission denied for id (823132282)
% 0.20/0.50  ipcrm: permission denied for id (825589883)
% 0.20/0.50  ipcrm: permission denied for id (825622652)
% 0.20/0.50  ipcrm: permission denied for id (823230591)
% 0.91/0.62  % (27725)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.91/0.63  % (27734)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.91/0.64  % (27734)Refutation not found, incomplete strategy% (27734)------------------------------
% 0.91/0.64  % (27734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.91/0.64  % (27734)Termination reason: Refutation not found, incomplete strategy
% 0.91/0.64  
% 0.91/0.64  % (27734)Memory used [KB]: 10618
% 0.91/0.64  % (27734)Time elapsed: 0.077 s
% 0.91/0.64  % (27734)------------------------------
% 0.91/0.64  % (27734)------------------------------
% 0.91/0.64  % (27723)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.91/0.64  % (27716)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.91/0.64  % (27716)Refutation not found, incomplete strategy% (27716)------------------------------
% 0.91/0.64  % (27716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.91/0.64  % (27716)Termination reason: Refutation not found, incomplete strategy
% 0.91/0.64  
% 0.91/0.64  % (27716)Memory used [KB]: 6140
% 0.91/0.64  % (27716)Time elapsed: 0.087 s
% 0.91/0.64  % (27716)------------------------------
% 0.91/0.64  % (27716)------------------------------
% 1.26/0.65  % (27739)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.65  % (27715)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.26/0.65  % (27739)Refutation not found, incomplete strategy% (27739)------------------------------
% 1.26/0.65  % (27739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.65  % (27739)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.65  
% 1.26/0.65  % (27739)Memory used [KB]: 6268
% 1.26/0.65  % (27739)Time elapsed: 0.105 s
% 1.26/0.65  % (27739)------------------------------
% 1.26/0.65  % (27739)------------------------------
% 1.26/0.65  % (27724)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.26/0.65  % (27731)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 1.26/0.66  % (27726)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.26/0.66  % (27718)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.26/0.67  % (27717)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.26/0.67  % (27732)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.67  % (27717)Refutation not found, incomplete strategy% (27717)------------------------------
% 1.26/0.67  % (27717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.67  % (27717)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.67  
% 1.26/0.67  % (27717)Memory used [KB]: 6140
% 1.26/0.67  % (27717)Time elapsed: 0.001 s
% 1.26/0.67  % (27717)------------------------------
% 1.26/0.67  % (27717)------------------------------
% 1.26/0.67  % (27722)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.26/0.67  % (27722)Refutation not found, incomplete strategy% (27722)------------------------------
% 1.26/0.67  % (27722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.67  % (27722)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.67  
% 1.26/0.67  % (27722)Memory used [KB]: 6140
% 1.26/0.67  % (27722)Time elapsed: 0.115 s
% 1.26/0.67  % (27722)------------------------------
% 1.26/0.67  % (27722)------------------------------
% 1.26/0.67  % (27724)Refutation found. Thanks to Tanya!
% 1.26/0.67  % SZS status Theorem for theBenchmark
% 1.26/0.67  % SZS output start Proof for theBenchmark
% 1.26/0.67  fof(f344,plain,(
% 1.26/0.67    $false),
% 1.26/0.67    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f120,f125,f144,f262,f343])).
% 1.26/0.67  fof(f343,plain,(
% 1.26/0.67    ~spl5_14 | ~spl5_6),
% 1.26/0.67    inference(avatar_split_clause,[],[f339,f122,f257])).
% 1.26/0.67  fof(f257,plain,(
% 1.26/0.67    spl5_14 <=> r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0))),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.26/0.67  fof(f122,plain,(
% 1.26/0.67    spl5_6 <=> r2_hidden(sK3(sK0,sK1),sK0)),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.26/0.67  fof(f339,plain,(
% 1.26/0.67    ~r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0)) | ~spl5_6),
% 1.26/0.67    inference(superposition,[],[f145,f78])).
% 1.26/0.67  fof(f78,plain,(
% 1.26/0.67    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.26/0.67    inference(definition_unfolding,[],[f48,f74])).
% 1.26/0.67  fof(f74,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.26/0.67    inference(definition_unfolding,[],[f50,f73])).
% 1.26/0.67  fof(f73,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f51,f72])).
% 1.26/0.67  fof(f72,plain,(
% 1.26/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f58,f71])).
% 1.26/0.67  fof(f71,plain,(
% 1.26/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f65,f70])).
% 1.26/0.67  fof(f70,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f66,f69])).
% 1.26/0.67  fof(f69,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f67,f68])).
% 1.26/0.67  fof(f68,plain,(
% 1.26/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f14])).
% 1.26/0.67  fof(f14,axiom,(
% 1.26/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.26/0.67  fof(f67,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f13])).
% 1.26/0.67  fof(f13,axiom,(
% 1.26/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.26/0.67  fof(f66,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f12])).
% 1.26/0.67  fof(f12,axiom,(
% 1.26/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.26/0.67  fof(f65,plain,(
% 1.26/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f11])).
% 1.26/0.67  fof(f11,axiom,(
% 1.26/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.26/0.67  fof(f58,plain,(
% 1.26/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f10])).
% 1.26/0.67  fof(f10,axiom,(
% 1.26/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.26/0.67  fof(f51,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f9])).
% 1.26/0.67  fof(f9,axiom,(
% 1.26/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.26/0.67  fof(f50,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.26/0.67    inference(cnf_transformation,[],[f15])).
% 1.26/0.67  fof(f15,axiom,(
% 1.26/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.26/0.67  fof(f48,plain,(
% 1.26/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.26/0.67    inference(cnf_transformation,[],[f19])).
% 1.26/0.67  fof(f19,plain,(
% 1.26/0.67    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.26/0.67    inference(rectify,[],[f3])).
% 1.26/0.67  fof(f3,axiom,(
% 1.26/0.67    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.26/0.67  fof(f145,plain,(
% 1.26/0.67    ( ! [X0] : (~r2_hidden(sK3(sK0,sK1),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0))))) ) | ~spl5_6),
% 1.26/0.67    inference(unit_resulting_resolution,[],[f124,f87])).
% 1.26/0.67  fof(f87,plain,(
% 1.26/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.26/0.67    inference(equality_resolution,[],[f84])).
% 1.26/0.67  fof(f84,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 1.26/0.67    inference(definition_unfolding,[],[f60,f75])).
% 1.26/0.67  fof(f75,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.26/0.67    inference(definition_unfolding,[],[f52,f74])).
% 1.26/0.67  fof(f52,plain,(
% 1.26/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.26/0.67    inference(cnf_transformation,[],[f5])).
% 1.26/0.67  fof(f5,axiom,(
% 1.26/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.26/0.67  fof(f60,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.26/0.67    inference(cnf_transformation,[],[f40])).
% 1.26/0.67  fof(f40,plain,(
% 1.26/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.26/0.67  fof(f39,plain,(
% 1.26/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.26/0.67    introduced(choice_axiom,[])).
% 1.26/0.67  fof(f38,plain,(
% 1.26/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.26/0.67    inference(rectify,[],[f37])).
% 1.26/0.67  fof(f37,plain,(
% 1.26/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.26/0.67    inference(flattening,[],[f36])).
% 1.26/0.67  fof(f36,plain,(
% 1.26/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.26/0.67    inference(nnf_transformation,[],[f2])).
% 1.26/0.67  fof(f2,axiom,(
% 1.26/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.26/0.67  fof(f124,plain,(
% 1.26/0.67    r2_hidden(sK3(sK0,sK1),sK0) | ~spl5_6),
% 1.26/0.67    inference(avatar_component_clause,[],[f122])).
% 1.26/0.67  fof(f262,plain,(
% 1.26/0.67    spl5_14 | spl5_5 | ~spl5_6 | ~spl5_8),
% 1.26/0.67    inference(avatar_split_clause,[],[f261,f141,f122,f117,f257])).
% 1.26/0.67  fof(f117,plain,(
% 1.26/0.67    spl5_5 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.26/0.67  fof(f141,plain,(
% 1.26/0.67    spl5_8 <=> sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.26/0.67  fof(f261,plain,(
% 1.26/0.67    r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0)) | (spl5_5 | ~spl5_6 | ~spl5_8)),
% 1.26/0.67    inference(subsumption_resolution,[],[f250,f119])).
% 1.26/0.67  fof(f119,plain,(
% 1.26/0.67    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_5),
% 1.26/0.67    inference(avatar_component_clause,[],[f117])).
% 1.26/0.67  fof(f250,plain,(
% 1.26/0.67    r2_hidden(sK3(sK0,sK1),sK1) | r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK0)) | (~spl5_6 | ~spl5_8)),
% 1.26/0.67    inference(resolution,[],[f175,f124])).
% 1.26/0.67  fof(f175,plain,(
% 1.26/0.67    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,sK1) | r2_hidden(X3,k5_xboole_0(sK0,sK0))) ) | ~spl5_8),
% 1.26/0.67    inference(superposition,[],[f86,f143])).
% 1.26/0.67  fof(f143,plain,(
% 1.26/0.67    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_8),
% 1.26/0.67    inference(avatar_component_clause,[],[f141])).
% 1.26/0.67  fof(f86,plain,(
% 1.26/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.26/0.67    inference(equality_resolution,[],[f83])).
% 1.26/0.67  fof(f83,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 1.26/0.67    inference(definition_unfolding,[],[f61,f75])).
% 1.26/0.67  fof(f61,plain,(
% 1.26/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.26/0.67    inference(cnf_transformation,[],[f40])).
% 1.26/0.67  fof(f144,plain,(
% 1.26/0.67    spl5_8 | spl5_2 | ~spl5_3 | spl5_4),
% 1.26/0.67    inference(avatar_split_clause,[],[f137,f105,f100,f95,f141])).
% 1.26/0.67  fof(f95,plain,(
% 1.26/0.67    spl5_2 <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.26/0.67  fof(f100,plain,(
% 1.26/0.67    spl5_3 <=> v1_zfmisc_1(sK0)),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.26/0.67  fof(f105,plain,(
% 1.26/0.67    spl5_4 <=> v1_xboole_0(sK0)),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.26/0.67  fof(f137,plain,(
% 1.26/0.67    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl5_2 | ~spl5_3 | spl5_4)),
% 1.26/0.67    inference(unit_resulting_resolution,[],[f102,f107,f79,f97,f47])).
% 1.26/0.67  fof(f47,plain,(
% 1.26/0.67    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f23])).
% 1.26/0.67  fof(f23,plain,(
% 1.26/0.67    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.26/0.67    inference(flattening,[],[f22])).
% 1.26/0.67  fof(f22,plain,(
% 1.26/0.67    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.26/0.67    inference(ennf_transformation,[],[f16])).
% 1.26/0.67  fof(f16,axiom,(
% 1.26/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.26/0.67  fof(f97,plain,(
% 1.26/0.67    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl5_2),
% 1.26/0.67    inference(avatar_component_clause,[],[f95])).
% 1.26/0.67  fof(f79,plain,(
% 1.26/0.67    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.26/0.67    inference(definition_unfolding,[],[f49,f74])).
% 1.26/0.67  fof(f49,plain,(
% 1.26/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f6])).
% 1.26/0.67  fof(f6,axiom,(
% 1.26/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.26/0.67  fof(f107,plain,(
% 1.26/0.67    ~v1_xboole_0(sK0) | spl5_4),
% 1.26/0.67    inference(avatar_component_clause,[],[f105])).
% 1.26/0.67  fof(f102,plain,(
% 1.26/0.67    v1_zfmisc_1(sK0) | ~spl5_3),
% 1.26/0.67    inference(avatar_component_clause,[],[f100])).
% 1.26/0.67  fof(f125,plain,(
% 1.26/0.67    spl5_6 | spl5_1),
% 1.26/0.67    inference(avatar_split_clause,[],[f112,f90,f122])).
% 1.26/0.67  fof(f90,plain,(
% 1.26/0.67    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.26/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.26/0.67  fof(f112,plain,(
% 1.26/0.67    r2_hidden(sK3(sK0,sK1),sK0) | spl5_1),
% 1.26/0.67    inference(unit_resulting_resolution,[],[f92,f56])).
% 1.26/0.67  fof(f56,plain,(
% 1.26/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f35])).
% 1.26/0.67  fof(f35,plain,(
% 1.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.26/0.67  fof(f34,plain,(
% 1.26/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.26/0.67    introduced(choice_axiom,[])).
% 1.26/0.67  fof(f33,plain,(
% 1.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.26/0.67    inference(rectify,[],[f32])).
% 1.26/0.67  fof(f32,plain,(
% 1.26/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.26/0.67    inference(nnf_transformation,[],[f25])).
% 1.26/0.67  fof(f25,plain,(
% 1.26/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.26/0.67    inference(ennf_transformation,[],[f1])).
% 1.26/0.67  fof(f1,axiom,(
% 1.26/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.26/0.67  fof(f92,plain,(
% 1.26/0.67    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.26/0.67    inference(avatar_component_clause,[],[f90])).
% 1.26/0.67  fof(f120,plain,(
% 1.26/0.67    ~spl5_5 | spl5_1),
% 1.26/0.67    inference(avatar_split_clause,[],[f113,f90,f117])).
% 1.26/0.67  fof(f113,plain,(
% 1.26/0.67    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_1),
% 1.26/0.67    inference(unit_resulting_resolution,[],[f92,f57])).
% 1.26/0.67  fof(f57,plain,(
% 1.26/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.26/0.67    inference(cnf_transformation,[],[f35])).
% 1.26/0.67  fof(f108,plain,(
% 1.26/0.67    ~spl5_4),
% 1.26/0.67    inference(avatar_split_clause,[],[f41,f105])).
% 1.26/0.67  fof(f41,plain,(
% 1.26/0.67    ~v1_xboole_0(sK0)),
% 1.26/0.67    inference(cnf_transformation,[],[f28])).
% 1.26/0.67  fof(f28,plain,(
% 1.26/0.67    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 1.26/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27,f26])).
% 1.26/0.67  fof(f26,plain,(
% 1.26/0.67    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 1.26/0.67    introduced(choice_axiom,[])).
% 1.26/0.67  fof(f27,plain,(
% 1.26/0.67    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 1.26/0.67    introduced(choice_axiom,[])).
% 1.26/0.67  fof(f21,plain,(
% 1.26/0.67    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.26/0.67    inference(flattening,[],[f20])).
% 1.26/0.67  fof(f20,plain,(
% 1.26/0.67    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.26/0.67    inference(ennf_transformation,[],[f18])).
% 1.26/0.67  fof(f18,negated_conjecture,(
% 1.26/0.67    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.26/0.67    inference(negated_conjecture,[],[f17])).
% 1.26/0.67  fof(f17,conjecture,(
% 1.26/0.67    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.26/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 1.26/0.67  fof(f103,plain,(
% 1.26/0.67    spl5_3),
% 1.26/0.67    inference(avatar_split_clause,[],[f42,f100])).
% 1.26/0.67  fof(f42,plain,(
% 1.26/0.67    v1_zfmisc_1(sK0)),
% 1.26/0.67    inference(cnf_transformation,[],[f28])).
% 1.26/0.67  fof(f98,plain,(
% 1.26/0.67    ~spl5_2),
% 1.26/0.67    inference(avatar_split_clause,[],[f76,f95])).
% 1.26/0.67  fof(f76,plain,(
% 1.26/0.67    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.26/0.67    inference(definition_unfolding,[],[f43,f74])).
% 1.26/0.67  fof(f43,plain,(
% 1.26/0.67    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.26/0.67    inference(cnf_transformation,[],[f28])).
% 1.26/0.67  fof(f93,plain,(
% 1.26/0.67    ~spl5_1),
% 1.26/0.67    inference(avatar_split_clause,[],[f44,f90])).
% 1.26/0.67  fof(f44,plain,(
% 1.26/0.67    ~r1_tarski(sK0,sK1)),
% 1.26/0.67    inference(cnf_transformation,[],[f28])).
% 1.26/0.67  % SZS output end Proof for theBenchmark
% 1.26/0.67  % (27724)------------------------------
% 1.26/0.67  % (27724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.67  % (27724)Termination reason: Refutation
% 1.26/0.67  
% 1.26/0.67  % (27724)Memory used [KB]: 6396
% 1.26/0.67  % (27724)Time elapsed: 0.097 s
% 1.26/0.67  % (27724)------------------------------
% 1.26/0.67  % (27724)------------------------------
% 1.26/0.67  % (27733)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.26/0.68  % (27579)Success in time 0.324 s
%------------------------------------------------------------------------------
