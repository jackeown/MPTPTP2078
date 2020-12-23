%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 318 expanded)
%              Number of leaves         :   40 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  383 ( 830 expanded)
%              Number of equality atoms :   48 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f95,f100,f105,f130,f135,f141,f168,f183,f221,f239,f256,f284,f377,f394,f502,f600,f706,f876])).

fof(f876,plain,
    ( spl6_4
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | spl6_4
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f833,f104])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f833,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(resolution,[],[f792,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f792,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(superposition,[],[f516,f705])).

fof(f705,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl6_36
  <=> sK0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f516,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f515,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f515,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f509,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f509,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f429,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f429,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f409,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f409,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f393,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f393,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl6_24
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f706,plain,
    ( spl6_36
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f689,f597,f165,f703])).

fof(f165,plain,
    ( spl6_10
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f597,plain,
    ( spl6_32
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f689,plain,
    ( sK0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f167,f599])).

fof(f599,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f597])).

fof(f167,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f600,plain,
    ( spl6_32
    | ~ spl6_3
    | spl6_4
    | spl6_29 ),
    inference(avatar_split_clause,[],[f591,f487,f102,f97,f597])).

fof(f97,plain,
    ( spl6_3
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f487,plain,
    ( spl6_29
  <=> v1_xboole_0(k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f591,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl6_3
    | spl6_4
    | spl6_29 ),
    inference(unit_resulting_resolution,[],[f99,f104,f55,f489,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f489,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,sK1))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f487])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f99,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f502,plain,
    ( ~ spl6_29
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f484,f253,f487])).

fof(f253,plain,
    ( spl6_18
  <=> r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f484,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(resolution,[],[f255,f53])).

fof(f255,plain,
    ( r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f253])).

fof(f394,plain,
    ( spl6_24
    | ~ spl6_3
    | spl6_4
    | spl6_23 ),
    inference(avatar_split_clause,[],[f388,f374,f102,f97,f391])).

fof(f374,plain,
    ( spl6_23
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f388,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_3
    | spl6_4
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f104,f99,f50,f376,f52])).

fof(f376,plain,
    ( k1_xboole_0 != sK0
    | spl6_23 ),
    inference(avatar_component_clause,[],[f374])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f377,plain,
    ( ~ spl6_23
    | spl6_22 ),
    inference(avatar_split_clause,[],[f369,f280,f374])).

fof(f280,plain,
    ( spl6_22
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f369,plain,
    ( k1_xboole_0 != sK0
    | spl6_22 ),
    inference(superposition,[],[f282,f51])).

fof(f282,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f284,plain,
    ( ~ spl6_22
    | spl6_16 ),
    inference(avatar_split_clause,[],[f266,f236,f280])).

fof(f236,plain,
    ( spl6_16
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f266,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl6_16 ),
    inference(resolution,[],[f238,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f238,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f256,plain,
    ( spl6_18
    | spl6_15 ),
    inference(avatar_split_clause,[],[f241,f217,f253])).

fof(f217,plain,
    ( spl6_15
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f241,plain,
    ( r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1))
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f219,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f219,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f239,plain,
    ( ~ spl6_16
    | ~ spl6_7
    | spl6_12 ),
    inference(avatar_split_clause,[],[f233,f180,f132,f236])).

fof(f132,plain,
    ( spl6_7
  <=> r2_hidden(sK5(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f180,plain,
    ( spl6_12
  <=> r2_hidden(sK5(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f233,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl6_7
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f134,f182,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f182,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k1_xboole_0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f134,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f221,plain,
    ( ~ spl6_15
    | spl6_8 ),
    inference(avatar_split_clause,[],[f212,f137,f217])).

fof(f137,plain,
    ( spl6_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f212,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f50,f139,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f183,plain,
    ( ~ spl6_12
    | spl6_6 ),
    inference(avatar_split_clause,[],[f174,f127,f180])).

fof(f127,plain,
    ( spl6_6
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f174,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k1_xboole_0)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f50,f129,f68])).

fof(f129,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f168,plain,
    ( spl6_10
    | spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f158,f102,f97,f92,f165])).

fof(f92,plain,
    ( spl6_2
  <=> v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f158,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f99,f104,f55,f94,f52])).

fof(f94,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f141,plain,
    ( ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f123,f86,f137])).

fof(f86,plain,
    ( spl6_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f123,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl6_1 ),
    inference(resolution,[],[f88,f71])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f135,plain,
    ( spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f121,f86,f132])).

fof(f121,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f88,f69])).

fof(f130,plain,
    ( ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f122,f86,f127])).

fof(f122,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f46,f102])).

fof(f46,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f100,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f90,f92])).

fof(f90,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f78,f80])).

fof(f78,plain,(
    ~ v1_xboole_0(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f48,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10657)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.48  % (10665)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.50  % (10665)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f877,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f89,f95,f100,f105,f130,f135,f141,f168,f183,f221,f239,f256,f284,f377,f394,f502,f600,f706,f876])).
% 0.22/0.51  fof(f876,plain,(
% 0.22/0.51    spl6_4 | ~spl6_24 | ~spl6_36),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f875])).
% 0.22/0.51  fof(f875,plain,(
% 0.22/0.51    $false | (spl6_4 | ~spl6_24 | ~spl6_36)),
% 0.22/0.51    inference(subsumption_resolution,[],[f833,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl6_4 <=> v1_xboole_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f833,plain,(
% 0.22/0.51    v1_xboole_0(sK0) | (~spl6_24 | ~spl6_36)),
% 0.22/0.51    inference(resolution,[],[f792,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(rectify,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f792,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK0)) ) | (~spl6_24 | ~spl6_36)),
% 0.22/0.51    inference(superposition,[],[f516,f705])).
% 0.22/0.51  fof(f705,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK0) | ~spl6_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f703])).
% 0.22/0.51  fof(f703,plain,(
% 0.22/0.51    spl6_36 <=> sK0 = k4_xboole_0(sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.51  fof(f516,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) ) | ~spl6_24),
% 0.22/0.51    inference(forward_demodulation,[],[f515,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.51  fof(f515,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) ) | ~spl6_24),
% 0.22/0.51    inference(forward_demodulation,[],[f509,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f59,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f58,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f57,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f73,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f509,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)))) ) | ~spl6_24),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f429,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f61,f77])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.51  fof(f429,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_24),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f409,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_24),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f393,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f393,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0) | ~spl6_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f391])).
% 0.22/0.51  fof(f391,plain,(
% 0.22/0.51    spl6_24 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.51  fof(f706,plain,(
% 0.22/0.51    spl6_36 | ~spl6_10 | ~spl6_32),
% 0.22/0.51    inference(avatar_split_clause,[],[f689,f597,f165,f703])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl6_10 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f597,plain,(
% 0.22/0.51    spl6_32 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.51  fof(f689,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK0) | (~spl6_10 | ~spl6_32)),
% 0.22/0.51    inference(backward_demodulation,[],[f167,f599])).
% 0.22/0.51  fof(f599,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK1) | ~spl6_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f597])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f165])).
% 0.22/0.51  fof(f600,plain,(
% 0.22/0.51    spl6_32 | ~spl6_3 | spl6_4 | spl6_29),
% 0.22/0.51    inference(avatar_split_clause,[],[f591,f487,f102,f97,f597])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl6_3 <=> v1_zfmisc_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f487,plain,(
% 0.22/0.51    spl6_29 <=> v1_xboole_0(k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.51  fof(f591,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK1) | (~spl6_3 | spl6_4 | spl6_29)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f104,f55,f489,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.51  fof(f489,plain,(
% 0.22/0.51    ~v1_xboole_0(k4_xboole_0(sK0,sK1)) | spl6_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f487])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    v1_zfmisc_1(sK0) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    ~spl6_29 | ~spl6_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f484,f253,f487])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    spl6_18 <=> r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.51  fof(f484,plain,(
% 0.22/0.51    ~v1_xboole_0(k4_xboole_0(sK0,sK1)) | ~spl6_18),
% 0.22/0.51    inference(resolution,[],[f255,f53])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1)) | ~spl6_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f253])).
% 0.22/0.51  fof(f394,plain,(
% 0.22/0.51    spl6_24 | ~spl6_3 | spl6_4 | spl6_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f388,f374,f102,f97,f391])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    spl6_23 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.51  fof(f388,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0) | (~spl6_3 | spl6_4 | spl6_23)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f104,f99,f50,f376,f52])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl6_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f374])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f377,plain,(
% 0.22/0.51    ~spl6_23 | spl6_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f369,f280,f374])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    spl6_22 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.51  fof(f369,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl6_22),
% 0.22/0.51    inference(superposition,[],[f282,f51])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | spl6_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f280])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ~spl6_22 | spl6_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f266,f236,f280])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    spl6_16 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | spl6_16),
% 0.22/0.51    inference(resolution,[],[f238,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.51    inference(nnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~r1_tarski(sK0,k1_xboole_0) | spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f236])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    spl6_18 | spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f241,f217,f253])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    spl6_15 <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    r2_hidden(sK5(k4_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,sK1)) | spl6_15),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f219,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f217])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ~spl6_16 | ~spl6_7 | spl6_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f233,f180,f132,f236])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl6_7 <=> r2_hidden(sK5(sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    spl6_12 <=> r2_hidden(sK5(sK0,sK1),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ~r1_tarski(sK0,k1_xboole_0) | (~spl6_7 | spl6_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f134,f182,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1),k1_xboole_0) | spl6_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f180])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    r2_hidden(sK5(sK0,sK1),sK0) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ~spl6_15 | spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f212,f137,f217])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl6_8 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl6_8),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f50,f139,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~spl6_12 | spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f174,f127,f180])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl6_6 <=> r2_hidden(sK5(sK0,sK1),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1),k1_xboole_0) | spl6_6),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f50,f129,f68])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1),sK1) | spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    spl6_10 | spl6_2 | ~spl6_3 | spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f158,f102,f97,f92,f165])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl6_2 <=> v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (spl6_2 | ~spl6_3 | spl6_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f104,f55,f94,f52])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~spl6_8 | spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f123,f86,f137])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl6_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl6_1),
% 0.22/0.51    inference(resolution,[],[f88,f71])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK1) | spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl6_7 | spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f86,f132])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    r2_hidden(sK5(sK0,sK1),sK0) | spl6_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f69])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ~spl6_6 | spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f122,f86,f127])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1),sK1) | spl6_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f102])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f17])).
% 0.22/0.51  fof(f17,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f97])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v1_zfmisc_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f90,f92])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.51    inference(forward_demodulation,[],[f78,f80])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.22/0.51    inference(definition_unfolding,[],[f48,f77])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f86])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (10665)------------------------------
% 0.22/0.51  % (10665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10665)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (10665)Memory used [KB]: 6524
% 0.22/0.51  % (10665)Time elapsed: 0.084 s
% 0.22/0.51  % (10665)------------------------------
% 0.22/0.51  % (10665)------------------------------
% 0.22/0.51  % (10633)Success in time 0.155 s
%------------------------------------------------------------------------------
