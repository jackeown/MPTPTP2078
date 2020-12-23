%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t9_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  46 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  90 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f33,f44,f53,f61])).

fof(f61,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f25,plain,
    ( sK1 != sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( sK1 = sK2
    | ~ spl3_6 ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,
    ( ! [X6] :
        ( k1_tarski(sK1) != k1_tarski(X6)
        | sK2 = X6 )
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f52])).

fof(f52,plain,
    ( k1_tarski(sK1) = k2_tarski(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_6
  <=> k1_tarski(sK1) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f35,plain,(
    ! [X2,X3,X1] :
      ( k1_tarski(X3) != k2_tarski(X2,X1)
      | X1 = X3 ) ),
    inference(superposition,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t9_zfmisc_1.p',commutativity_k2_tarski)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t9_zfmisc_1.p',t8_zfmisc_1)).

fof(f53,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f46,f42,f31,f51])).

fof(f31,plain,
    ( spl3_2
  <=> k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( k1_tarski(sK1) = k2_tarski(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f43,f32])).

fof(f32,plain,
    ( k1_tarski(sK0) = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f43,plain,
    ( sK0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f31,f42])).

fof(f37,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != k1_tarski(X0)
        | sK1 = X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f19,f32])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t9_zfmisc_1.p',t9_zfmisc_1)).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f24])).

fof(f17,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
