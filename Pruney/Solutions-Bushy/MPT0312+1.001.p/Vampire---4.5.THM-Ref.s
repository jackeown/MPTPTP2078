%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0312+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   52 (  81 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  118 ( 199 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f35,f39,f43,f50,f55,f76,f126])).

fof(f126,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f123,f49])).

fof(f49,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_7
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f123,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK2,sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f113,f34])).

fof(f34,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f113,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2))
    | spl4_1
    | ~ spl4_11 ),
    inference(superposition,[],[f20,f75])).

fof(f75,plain,
    ( ! [X10,X11] : k3_xboole_0(k2_zfmisc_1(sK0,X10),k2_zfmisc_1(sK1,X11)) = k2_zfmisc_1(sK0,k3_xboole_0(X10,X11))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_11
  <=> ! [X11,X10] : k3_xboole_0(k2_zfmisc_1(sK0,X10),k2_zfmisc_1(sK1,X11)) = k2_zfmisc_1(sK0,k3_xboole_0(X10,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f20,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK2) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f76,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f59,f52,f41,f74])).

fof(f41,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f52,plain,
    ( spl4_8
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f59,plain,
    ( ! [X10,X11] : k3_xboole_0(k2_zfmisc_1(sK0,X10),k2_zfmisc_1(sK1,X11)) = k2_zfmisc_1(sK0,k3_xboole_0(X10,X11))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(superposition,[],[f42,f54])).

fof(f54,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f42,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f55,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f45,f37,f28,f52])).

fof(f28,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f37,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f45,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f50,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f44,f37,f23,f47])).

fof(f23,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f43,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f39,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f35,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f26,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f18])).

fof(f13,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
