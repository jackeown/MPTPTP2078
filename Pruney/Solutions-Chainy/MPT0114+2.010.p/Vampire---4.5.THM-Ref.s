%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  184 ( 312 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f63,f466,f467,f483,f737,f746,f754,f883,f1409])).

fof(f1409,plain,
    ( ~ spl3_2
    | spl3_1
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f1405,f879,f50,f54])).

fof(f54,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f879,plain,
    ( spl3_64
  <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1405,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_64 ),
    inference(superposition,[],[f886,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f886,plain,
    ( ! [X2] :
        ( r1_tarski(sK0,k4_xboole_0(X2,k3_xboole_0(sK1,sK2)))
        | ~ r1_tarski(sK0,X2) )
    | ~ spl3_64 ),
    inference(superposition,[],[f46,f881])).

fof(f881,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f879])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f883,plain,
    ( spl3_64
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f874,f85,f879])).

fof(f85,plain,
    ( spl3_7
  <=> sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f874,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(superposition,[],[f35,f87])).

fof(f87,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f754,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f752,f58,f85])).

fof(f58,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f752,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f59,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f746,plain,
    ( spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f108,f90,f58])).

fof(f90,plain,
    ( spl3_8
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f92,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f737,plain,
    ( spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f735,f117,f90])).

fof(f117,plain,
    ( spl3_12
  <=> k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f735,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f406,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f406,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,k5_xboole_0(sK1,sK2))
        | r1_xboole_0(X2,sK0) )
    | ~ spl3_12 ),
    inference(superposition,[],[f44,f119])).

fof(f119,plain,
    ( k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f483,plain,
    ( spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f481,f122,f54])).

fof(f122,plain,
    ( spl3_13
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f481,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(superposition,[],[f315,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f315,plain,
    ( ! [X1] : r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),X1))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f310,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f310,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(k5_xboole_0(sK1,sK2),X1))
    | ~ spl3_13 ),
    inference(superposition,[],[f42,f124])).

fof(f124,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f42,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f467,plain,
    ( spl3_13
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f465,f50,f122])).

fof(f465,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f466,plain,
    ( spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f464,f50,f117])).

fof(f464,plain,
    ( k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f63,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f30,f54,f50])).

fof(f30,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f62,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f31,f58,f50])).

fof(f31,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f58,f54,f50])).

fof(f32,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (18924)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % (18921)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (18926)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (18925)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (18917)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (18930)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (18918)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (18928)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (18922)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (18931)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (18934)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (18923)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (18927)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (18920)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (18932)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (18929)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (18919)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (18928)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1415,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f61,f62,f63,f466,f467,f483,f737,f746,f754,f883,f1409])).
% 0.20/0.51  fof(f1409,plain,(
% 0.20/0.51    ~spl3_2 | spl3_1 | ~spl3_64),
% 0.20/0.51    inference(avatar_split_clause,[],[f1405,f879,f50,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f879,plain,(
% 0.20/0.51    spl3_64 <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.20/0.51  fof(f1405,plain,(
% 0.20/0.51    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_64),
% 0.20/0.51    inference(superposition,[],[f886,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.20/0.51  fof(f886,plain,(
% 0.20/0.51    ( ! [X2] : (r1_tarski(sK0,k4_xboole_0(X2,k3_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,X2)) ) | ~spl3_64),
% 0.20/0.51    inference(superposition,[],[f46,f881])).
% 0.20/0.51  fof(f881,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_64),
% 0.20/0.51    inference(avatar_component_clause,[],[f879])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.20/0.51  fof(f883,plain,(
% 0.20/0.51    spl3_64 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f874,f85,f879])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl3_7 <=> sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f874,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_7),
% 0.20/0.51    inference(superposition,[],[f35,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.51  fof(f754,plain,(
% 0.20/0.51    spl3_7 | ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f752,f58,f85])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl3_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f752,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f59,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f746,plain,(
% 0.20/0.51    spl3_3 | ~spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f108,f90,f58])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl3_8 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_8),
% 0.20/0.51    inference(resolution,[],[f92,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f737,plain,(
% 0.20/0.51    spl3_8 | ~spl3_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f735,f117,f90])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl3_12 <=> k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.51  fof(f735,plain,(
% 0.20/0.51    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_12),
% 0.20/0.51    inference(resolution,[],[f406,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    ( ! [X2] : (~r1_xboole_0(X2,k5_xboole_0(sK1,sK2)) | r1_xboole_0(X2,sK0)) ) | ~spl3_12),
% 0.20/0.51    inference(superposition,[],[f44,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.51  fof(f483,plain,(
% 0.20/0.51    spl3_2 | ~spl3_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f481,f122,f54])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl3_13 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.51  fof(f481,plain,(
% 0.20/0.51    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_13),
% 0.20/0.51    inference(superposition,[],[f315,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),X1))) ) | ~spl3_13),
% 0.20/0.51    inference(forward_demodulation,[],[f310,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.51  fof(f310,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(k5_xboole_0(sK1,sK2),X1))) ) | ~spl3_13),
% 0.20/0.51    inference(superposition,[],[f42,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.51  fof(f467,plain,(
% 0.20/0.51    spl3_13 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f465,f50,f122])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f51,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f466,plain,(
% 0.20/0.51    spl3_12 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f464,f50,f117])).
% 0.20/0.51  fof(f464,plain,(
% 0.20/0.51    k5_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f51,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl3_1 | spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f54,f50])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.51    inference(nnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl3_1 | spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f58,f50])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f58,f54,f50])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (18928)------------------------------
% 0.20/0.51  % (18928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18928)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (18928)Memory used [KB]: 11513
% 0.20/0.51  % (18928)Time elapsed: 0.110 s
% 0.20/0.51  % (18928)------------------------------
% 0.20/0.51  % (18928)------------------------------
% 0.20/0.51  % (18933)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.53  % (18916)Success in time 0.182 s
%------------------------------------------------------------------------------
