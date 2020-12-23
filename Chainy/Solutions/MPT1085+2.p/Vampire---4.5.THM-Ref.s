%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 121 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1812,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1778,f1782,f1786,f1811])).

fof(f1811,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f1810])).

fof(f1810,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f1807,f1781])).

fof(f1781,plain,
    ( v1_finset_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1780,plain,
    ( spl7_2
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1807,plain,
    ( ~ v1_finset_1(sK1)
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f1802,f1785])).

fof(f1785,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f1784,plain,
    ( spl7_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1802,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ v1_finset_1(X0) )
    | spl7_1 ),
    inference(resolution,[],[f1800,f1754])).

fof(f1754,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1731])).

fof(f1731,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1800,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ v1_finset_1(X0) )
    | spl7_1 ),
    inference(resolution,[],[f1750,f1777])).

fof(f1777,plain,
    ( ~ v1_finset_1(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f1776,plain,
    ( spl7_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1750,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1717])).

fof(f1717,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1708])).

fof(f1708,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

fof(f1786,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f1746,f1784])).

fof(f1746,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f1728])).

fof(f1728,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1716,f1727])).

fof(f1727,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(X1)
        & r1_tarski(X0,X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1716,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1715])).

fof(f1715,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1712])).

fof(f1712,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & r1_tarski(X0,X1) )
       => v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1711])).

fof(f1711,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f1782,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f1747,f1780])).

fof(f1747,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f1728])).

fof(f1778,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f1748,f1776])).

fof(f1748,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1728])).
%------------------------------------------------------------------------------
