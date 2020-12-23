%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t77_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 211 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f42,f49,f56,f102,f106])).

fof(f106,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl7_0
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f41,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl7_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f103,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl7_9 ),
    inference(resolution,[],[f101,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t77_mcart_1.p',t119_zfmisc_1)).

fof(f101,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_9
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f102,plain,
    ( ~ spl7_9
    | ~ spl7_4
    | spl7_7 ),
    inference(avatar_split_clause,[],[f93,f54,f47,f100])).

fof(f47,plain,
    ( spl7_4
  <=> r1_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f54,plain,
    ( spl7_7
  <=> ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f93,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f48,plain,
    ( r1_tarski(sK4,sK5)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f90,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl7_7 ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k3_zfmisc_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
      | ~ r1_tarski(X5,X2)
      | ~ r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f60,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t77_mcart_1.p',d3_zfmisc_1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k3_zfmisc_1(X0,X1,X2),k2_zfmisc_1(X3,X4))
      | ~ r1_tarski(X2,X4)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),X3) ) ),
    inference(superposition,[],[f28,f27])).

fof(f56,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f15])).

fof(f15,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t77_mcart_1.p',t77_mcart_1)).

fof(f49,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
