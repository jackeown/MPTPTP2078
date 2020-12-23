%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t6_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 257 expanded)
%              Number of equality atoms :   70 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f59,f66,f76,f98,f117,f133,f172,f183])).

fof(f183,plain,
    ( ~ spl3_0
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f173,f51])).

fof(f51,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f173,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_16 ),
    inference(superposition,[],[f29,f110])).

fof(f110,plain,
    ( k1_tarski(sK0) = o_0_0_xboole_0
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_16
  <=> k1_tarski(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',fc2_xboole_0)).

fof(f172,plain,
    ( spl3_3
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f168,f58])).

fof(f58,plain,
    ( sK0 != sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_3
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f168,plain,
    ( sK0 = sK1
    | ~ spl3_20 ),
    inference(resolution,[],[f132,f43])).

fof(f43,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',d1_tarski)).

fof(f132,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_20
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f133,plain,
    ( spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f120,f115,f131])).

fof(f115,plain,
    ( spl3_18
  <=> k1_tarski(sK0) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f120,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl3_18 ),
    inference(superposition,[],[f42,f116])).

fof(f116,plain,
    ( k1_tarski(sK0) = k1_tarski(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f42,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,
    ( spl3_16
    | spl3_18
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f99,f96,f64,f115,f109])).

fof(f64,plain,
    ( spl3_4
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f96,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( o_0_0_xboole_0 = X0
        | k1_tarski(X1) = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f99,plain,
    ( k1_tarski(sK0) = k1_tarski(sK1)
    | k1_tarski(sK0) = o_0_0_xboole_0
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tarski(X1))
        | k1_tarski(X1) = X0
        | o_0_0_xboole_0 = X0 )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f94,f74,f96])).

fof(f74,plain,
    ( spl3_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( o_0_0_xboole_0 = X0
        | k1_tarski(X1) = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f36,f75])).

fof(f75,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',l3_zfmisc_1)).

fof(f76,plain,
    ( spl3_6
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f67,f50,f74])).

fof(f67,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_0 ),
    inference(resolution,[],[f30,f51])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',t6_boole)).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',t6_zfmisc_1)).

fof(f59,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t6_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
