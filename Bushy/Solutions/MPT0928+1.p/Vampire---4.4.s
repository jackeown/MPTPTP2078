%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t88_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 290 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f55,f62,f71,f82])).

fof(f82,plain,
    ( ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_0
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f80,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f79,f47])).

fof(f47,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl9_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f79,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f78,f54])).

fof(f54,plain,
    ( r1_tarski(sK4,sK5)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl9_4
  <=> r1_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f78,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f61,plain,
    ( r1_tarski(sK6,sK7)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl9_6
  <=> r1_tarski(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f77,plain,
    ( ~ r1_tarski(sK6,sK7)
    | ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl9_9 ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_9
  <=> ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(k4_zfmisc_1(X2,X3,X4,X0),k4_zfmisc_1(X5,X6,X7,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X4,X7)
      | ~ r1_tarski(X3,X6)
      | ~ r1_tarski(X2,X5) ) ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t88_mcart_1.p',t77_mcart_1)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tarski(k3_zfmisc_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | ~ r1_tarski(X7,X3)
      | r1_tarski(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(superposition,[],[f72,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t88_mcart_1.p',d4_zfmisc_1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k4_zfmisc_1(X0,X1,X2,X3),k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X3,X5)
      | ~ r1_tarski(k3_zfmisc_1(X0,X1,X2),X4) ) ),
    inference(superposition,[],[f33,f32])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t88_mcart_1.p',t119_zfmisc_1)).

fof(f71,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
    & r1_tarski(sK6,sK7)
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
        & r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
      & r1_tarski(sK6,sK7)
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_tarski(X6,X7)
          & r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t88_mcart_1.p',t88_mcart_1)).

fof(f62,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
