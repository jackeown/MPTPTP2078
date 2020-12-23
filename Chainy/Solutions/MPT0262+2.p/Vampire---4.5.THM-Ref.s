%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0262+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 199 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f759,f764,f769,f777,f798,f811,f942,f979,f1174])).

fof(f1174,plain,
    ( spl15_4
    | ~ spl15_9
    | ~ spl15_10 ),
    inference(avatar_contradiction_clause,[],[f1173])).

fof(f1173,plain,
    ( $false
    | spl15_4
    | ~ spl15_9
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f1172,f776])).

fof(f776,plain,
    ( ~ r1_xboole_0(sK1,k2_tarski(sK0,sK2))
    | spl15_4 ),
    inference(avatar_component_clause,[],[f774])).

fof(f774,plain,
    ( spl15_4
  <=> r1_xboole_0(sK1,k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f1172,plain,
    ( r1_xboole_0(sK1,k2_tarski(sK0,sK2))
    | ~ spl15_9
    | ~ spl15_10 ),
    inference(forward_demodulation,[],[f1159,f581])).

fof(f581,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1159,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ spl15_9
    | ~ spl15_10 ),
    inference(unit_resulting_resolution,[],[f978,f941,f549])).

fof(f549,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f394])).

fof(f394,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f941,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl15_9
  <=> r1_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f978,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK2))
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl15_10
  <=> r1_xboole_0(sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f979,plain,
    ( spl15_10
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f835,f808,f976])).

fof(f808,plain,
    ( spl15_6
  <=> r1_xboole_0(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f835,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK2))
    | ~ spl15_6 ),
    inference(unit_resulting_resolution,[],[f810,f559])).

fof(f559,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f400])).

fof(f400,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f810,plain,
    ( r1_xboole_0(k1_tarski(sK2),sK1)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f808])).

fof(f942,plain,
    ( spl15_9
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f821,f795,f939])).

fof(f795,plain,
    ( spl15_5
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f821,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl15_5 ),
    inference(unit_resulting_resolution,[],[f797,f559])).

fof(f797,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f795])).

fof(f811,plain,
    ( spl15_6
    | spl15_2 ),
    inference(avatar_split_clause,[],[f792,f761,f808])).

fof(f761,plain,
    ( spl15_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f792,plain,
    ( r1_xboole_0(k1_tarski(sK2),sK1)
    | spl15_2 ),
    inference(unit_resulting_resolution,[],[f763,f560])).

fof(f560,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f357])).

fof(f357,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f763,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f761])).

fof(f798,plain,
    ( spl15_5
    | spl15_1 ),
    inference(avatar_split_clause,[],[f791,f756,f795])).

fof(f756,plain,
    ( spl15_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f791,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | spl15_1 ),
    inference(unit_resulting_resolution,[],[f758,f560])).

fof(f758,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f756])).

fof(f777,plain,
    ( ~ spl15_4
    | spl15_3 ),
    inference(avatar_split_clause,[],[f770,f766,f774])).

fof(f766,plain,
    ( spl15_3
  <=> r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f770,plain,
    ( ~ r1_xboole_0(sK1,k2_tarski(sK0,sK2))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f768,f559])).

fof(f768,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl15_3 ),
    inference(avatar_component_clause,[],[f766])).

fof(f769,plain,(
    ~ spl15_3 ),
    inference(avatar_split_clause,[],[f525,f766])).

fof(f525,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f472])).

fof(f472,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ~ r2_hidden(sK2,sK1)
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f367,f471])).

fof(f471,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f367,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
      & ~ r2_hidden(X2,X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f359])).

fof(f359,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f358])).

fof(f358,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f764,plain,(
    ~ spl15_2 ),
    inference(avatar_split_clause,[],[f524,f761])).

fof(f524,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f472])).

fof(f759,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f523,f756])).

fof(f523,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f472])).
%------------------------------------------------------------------------------
