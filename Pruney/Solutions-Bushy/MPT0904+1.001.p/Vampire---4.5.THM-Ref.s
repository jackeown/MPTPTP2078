%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0904+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:52 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 112 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 312 expanded)
%              Number of equality atoms :    2 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f85,f87,f89,f91])).

fof(f91,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f17,f83])).

fof(f83,plain,(
    ~ r1_xboole_0(sK0,sK4) ),
    inference(resolution,[],[f81,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f81,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f69,f12])).

fof(f69,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f46,f9])).

fof(f9,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) ) ),
    inference(superposition,[],[f35,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f35,plain,(
    ! [X14,X12,X17,X15,X13,X16] :
      ( r1_xboole_0(k2_zfmisc_1(X16,X17),k4_zfmisc_1(X12,X13,X14,X15))
      | ~ r1_xboole_0(X16,k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14)) ) ),
    inference(superposition,[],[f12,f11])).

fof(f17,plain,
    ( r1_xboole_0(sK0,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl8_1
  <=> r1_xboole_0(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f89,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f39,f29])).

fof(f29,plain,
    ( r1_xboole_0(sK3,sK7)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl8_4
  <=> r1_xboole_0(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f39,plain,(
    ~ r1_xboole_0(sK3,sK7) ),
    inference(resolution,[],[f37,f9])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | ~ r1_xboole_0(X3,X7) ) ),
    inference(superposition,[],[f33,f11])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X4,X5),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ r1_xboole_0(X5,X3) ) ),
    inference(superposition,[],[f13,f11])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f80,f25])).

fof(f25,plain,
    ( r1_xboole_0(sK2,sK6)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl8_3
  <=> r1_xboole_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f80,plain,(
    ~ r1_xboole_0(sK2,sK6) ),
    inference(resolution,[],[f69,f13])).

fof(f85,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f21,f82])).

fof(f82,plain,(
    ~ r1_xboole_0(sK1,sK5) ),
    inference(resolution,[],[f81,f13])).

fof(f21,plain,
    ( r1_xboole_0(sK1,sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl8_2
  <=> r1_xboole_0(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f30,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f10,f27,f23,f19,f15])).

fof(f10,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
