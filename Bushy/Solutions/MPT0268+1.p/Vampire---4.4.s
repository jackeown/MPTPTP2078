%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t65_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:10 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (  91 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 198 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f59,f73,f74,f89,f99,f106,f114,f119])).

fof(f119,plain,
    ( ~ spl2_4
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f66,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = sK0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_4
  <=> k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f116,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != sK0
    | ~ spl2_13 ),
    inference(resolution,[],[f113,f81])).

fof(f81,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',t83_xboole_1)).

fof(f113,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_13
  <=> ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f114,plain,
    ( ~ spl2_13
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f90,f68,f112])).

fof(f68,plain,
    ( spl2_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f90,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',l24_zfmisc_1)).

fof(f69,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f106,plain,
    ( ~ spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f91,f68,f104])).

fof(f104,plain,
    ( spl2_11
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f99,plain,
    ( ~ spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f92,f68,f97])).

fof(f97,plain,
    ( spl2_9
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',t7_boole)).

fof(f89,plain,
    ( spl2_5
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f87,f63])).

fof(f63,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != sK0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_5
  <=> k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = sK0
    | ~ spl2_7 ),
    inference(resolution,[],[f79,f72])).

fof(f72,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_7
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f79,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | k4_xboole_0(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f40,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f37,f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',l27_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f31,f68,f62])).

fof(f31,plain,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
    & ( ~ r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
      & ( ~ r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',t65_zfmisc_1)).

fof(f73,plain,
    ( spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f30,f71,f65])).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f57,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',d2_xboole_0)).

fof(f52,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f45,f50])).

fof(f50,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t65_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
