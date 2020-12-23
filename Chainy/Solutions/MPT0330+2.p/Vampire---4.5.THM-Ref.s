%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0330+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 7.89s
% Output     : Refutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 237 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f550,f554,f558,f3563,f3564,f3727,f5263,f9631])).

fof(f9631,plain,
    ( ~ spl7_4
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f9583])).

fof(f9583,plain,
    ( $false
    | ~ spl7_4
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f978,f838,f949])).

fof(f949,plain,(
    ! [X47,X50,X48,X49] :
      ( ~ r1_tarski(X50,k2_zfmisc_1(X49,X48))
      | r1_tarski(X50,k2_zfmisc_1(k2_xboole_0(X47,X49),X48)) ) ),
    inference(superposition,[],[f499,f527])).

fof(f527,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f331])).

fof(f331,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f499,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f450])).

fof(f450,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f838,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f837])).

fof(f837,plain,
    ( spl7_11
  <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f978,plain,
    ( ! [X6] : r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(X6,sK5)))
    | ~ spl7_4 ),
    inference(superposition,[],[f619,f528])).

fof(f528,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f331])).

fof(f619,plain,
    ( ! [X3] : r1_tarski(sK1,k2_xboole_0(X3,k2_zfmisc_1(sK4,sK5)))
    | ~ spl7_4 ),
    inference(superposition,[],[f567,f608])).

fof(f608,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl7_4
  <=> k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f567,plain,(
    ! [X6,X7,X5] : r1_tarski(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7))) ),
    inference(resolution,[],[f497,f560])).

fof(f560,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f506,f489])).

fof(f489,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f506,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f497,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f448])).

fof(f448,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f5263,plain,
    ( ~ spl7_5
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f5250])).

fof(f5250,plain,
    ( $false
    | ~ spl7_5
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f835,f992,f1631,f496])).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f447])).

fof(f447,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f446])).

fof(f446,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1631,plain,
    ( ! [X0] : r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3))
    | ~ spl7_5 ),
    inference(superposition,[],[f1619,f527])).

fof(f1619,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(k2_zfmisc_1(sK2,sK3),X0))
    | ~ spl7_5 ),
    inference(superposition,[],[f1610,f489])).

fof(f1610,plain,
    ( ! [X10] : r1_tarski(sK0,k2_xboole_0(X10,k2_zfmisc_1(sK2,sK3)))
    | ~ spl7_5 ),
    inference(superposition,[],[f567,f612])).

fof(f612,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl7_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f992,plain,(
    ! [X54,X55,X53] : r1_tarski(k2_zfmisc_1(X53,X54),k2_zfmisc_1(X53,k2_xboole_0(X54,X55))) ),
    inference(superposition,[],[f506,f528])).

fof(f835,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f834])).

fof(f834,plain,
    ( spl7_10
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f3727,plain,
    ( ~ spl7_10
    | ~ spl7_11
    | spl7_1 ),
    inference(avatar_split_clause,[],[f3702,f548,f837,f834])).

fof(f548,plain,
    ( spl7_1
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f3702,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl7_1 ),
    inference(resolution,[],[f495,f549])).

fof(f549,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f548])).

fof(f495,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f445])).

fof(f445,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f444])).

fof(f444,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f3564,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f3562,f556,f611])).

fof(f556,plain,
    ( spl7_3
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f3562,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f505,f557])).

fof(f557,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f556])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f453])).

fof(f453,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3563,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f3561,f552,f607])).

fof(f552,plain,
    ( spl7_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3561,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl7_2 ),
    inference(resolution,[],[f505,f553])).

fof(f553,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f552])).

fof(f558,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f482,f556])).

fof(f482,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f475])).

fof(f475,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f439,f474])).

fof(f474,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f439,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f438])).

fof(f438,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f355])).

fof(f355,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f554,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f483,f552])).

fof(f483,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f475])).

fof(f550,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f484,f548])).

fof(f484,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f475])).
%------------------------------------------------------------------------------
