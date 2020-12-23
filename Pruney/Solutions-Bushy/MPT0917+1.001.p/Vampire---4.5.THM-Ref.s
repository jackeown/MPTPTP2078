%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0917+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  66 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 194 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f69,f95])).

fof(f95,plain,
    ( ~ spl6_5
    | ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f48,f19,f24,f50])).

fof(f50,plain,
    ( spl6_5
  <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f24,plain,
    ( spl6_2
  <=> r1_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f19,plain,
    ( spl6_1
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f48,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl6_1 ),
    inference(resolution,[],[f16,f21])).

fof(f21,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f69,plain,
    ( spl6_5
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f34,f29,f50])).

fof(f29,plain,
    ( spl6_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f34,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f43,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f36,f31,f16])).

fof(f31,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f37,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f11,f34])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_mcart_1)).

fof(f32,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f19])).

fof(f17,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    inference(definition_unfolding,[],[f14,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
