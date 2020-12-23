%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:10 EST 2020

% Result     : Theorem 12.59s
% Output     : Refutation 12.59s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 517 expanded)
%              Number of leaves         :   39 ( 170 expanded)
%              Depth                    :   16
%              Number of atoms          :  524 (2165 expanded)
%              Number of equality atoms :   46 ( 229 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f2355,f2601,f2733,f3691,f3707,f3799,f3826,f3856,f3861,f3940,f13299,f13319,f13384,f13409,f13418])).

fof(f13418,plain,
    ( spl7_148
    | ~ spl7_556 ),
    inference(avatar_split_clause,[],[f13414,f13407,f2410])).

fof(f2410,plain,
    ( spl7_148
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f13407,plain,
    ( spl7_556
  <=> r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_556])])).

fof(f13414,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl7_556 ),
    inference(resolution,[],[f13408,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13408,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ spl7_556 ),
    inference(avatar_component_clause,[],[f13407])).

fof(f13409,plain,
    ( spl7_556
    | ~ spl7_189
    | ~ spl7_554 ),
    inference(avatar_split_clause,[],[f13398,f13382,f2728,f13407])).

fof(f2728,plain,
    ( spl7_189
  <=> r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f13382,plain,
    ( spl7_554
  <=> r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_554])])).

fof(f13398,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ spl7_189
    | ~ spl7_554 ),
    inference(resolution,[],[f13387,f2729])).

fof(f2729,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))
    | ~ spl7_189 ),
    inference(avatar_component_clause,[],[f2728])).

fof(f13387,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X1)
        | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1) )
    | ~ spl7_554 ),
    inference(resolution,[],[f13383,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13383,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl7_554 ),
    inference(avatar_component_clause,[],[f13382])).

fof(f13384,plain,
    ( ~ spl7_2
    | spl7_554
    | ~ spl7_3
    | ~ spl7_550 ),
    inference(avatar_split_clause,[],[f13378,f13317,f108,f13382,f104])).

fof(f104,plain,
    ( spl7_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f108,plain,
    ( spl7_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f13317,plain,
    ( spl7_550
  <=> ! [X0] :
        ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_550])])).

fof(f13378,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ spl7_3
    | ~ spl7_550 ),
    inference(resolution,[],[f13318,f109])).

fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f13318,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl7_550 ),
    inference(avatar_component_clause,[],[f13317])).

fof(f13319,plain,
    ( ~ spl7_4
    | spl7_550
    | spl7_148 ),
    inference(avatar_split_clause,[],[f13309,f2410,f13317,f112])).

fof(f112,plain,
    ( spl7_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f13309,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl7_148 ),
    inference(resolution,[],[f13302,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f13302,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) )
    | spl7_148 ),
    inference(resolution,[],[f2411,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2) ) ),
    inference(resolution,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2411,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl7_148 ),
    inference(avatar_component_clause,[],[f2410])).

fof(f13299,plain,
    ( ~ spl7_148
    | ~ spl7_135
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f13296,f112,f108,f100,f2250,f2410])).

fof(f2250,plain,
    ( spl7_135
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f100,plain,
    ( spl7_1
  <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f13296,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f943,f109])).

fof(f943,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | r1_tarski(k3_relat_1(sK0),k3_relat_1(X7))
        | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X7))
        | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(X7)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f807,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_relat_1(X0))
      | ~ r1_tarski(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f75,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f807,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X1)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | r1_tarski(k3_relat_1(sK0),X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f141,f113])).

fof(f113,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | r1_tarski(k3_relat_1(X0),X1) ) ),
    inference(superposition,[],[f77,f57])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f3940,plain,(
    spl7_218 ),
    inference(avatar_contradiction_clause,[],[f3931])).

fof(f3931,plain,
    ( $false
    | spl7_218 ),
    inference(resolution,[],[f55,f3400])).

fof(f3400,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl7_218 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f3399,plain,
    ( spl7_218
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3861,plain,
    ( ~ spl7_218
    | spl7_239
    | ~ spl7_243 ),
    inference(avatar_split_clause,[],[f3860,f3854,f3824,f3399])).

fof(f3824,plain,
    ( spl7_239
  <=> r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_239])])).

fof(f3854,plain,
    ( spl7_243
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_243])])).

fof(f3860,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl7_239
    | ~ spl7_243 ),
    inference(forward_demodulation,[],[f3825,f3855])).

fof(f3855,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_243 ),
    inference(avatar_component_clause,[],[f3854])).

fof(f3825,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1))
    | spl7_239 ),
    inference(avatar_component_clause,[],[f3824])).

fof(f3856,plain,
    ( spl7_243
    | ~ spl7_173 ),
    inference(avatar_split_clause,[],[f3852,f2599,f3854])).

fof(f2599,plain,
    ( spl7_173
  <=> k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f3852,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_173 ),
    inference(forward_demodulation,[],[f3851,f3443])).

fof(f3443,plain,(
    ! [X26] : k1_xboole_0 = k6_subset_1(X26,X26) ),
    inference(resolution,[],[f3197,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f55])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3197,plain,(
    ! [X4,X3] : r1_tarski(k6_subset_1(X3,X3),X4) ),
    inference(duplicate_literal_removal,[],[f3190])).

fof(f3190,plain,(
    ! [X4,X3] :
      ( r1_tarski(k6_subset_1(X3,X3),X4)
      | r1_tarski(k6_subset_1(X3,X3),X4) ) ),
    inference(resolution,[],[f606,f67])).

fof(f606,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(sK2(k6_subset_1(X10,X11),X12),k6_subset_1(X13,X10))
      | r1_tarski(k6_subset_1(X10,X11),X12) ) ),
    inference(resolution,[],[f119,f97])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f79,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k6_subset_1(X0,X1),X2),X0)
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f98,f67])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f78,f62])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3851,plain,
    ( k1_xboole_0 = k1_relat_1(k6_subset_1(sK1,sK1))
    | ~ spl7_173 ),
    inference(forward_demodulation,[],[f2600,f3443])).

fof(f2600,plain,
    ( k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl7_173 ),
    inference(avatar_component_clause,[],[f2599])).

fof(f3826,plain,
    ( ~ spl7_239
    | spl7_190 ),
    inference(avatar_split_clause,[],[f3822,f2731,f3824])).

fof(f2731,plain,
    ( spl7_190
  <=> r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f3822,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1))
    | spl7_190 ),
    inference(forward_demodulation,[],[f2732,f3443])).

fof(f2732,plain,
    ( ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1))
    | spl7_190 ),
    inference(avatar_component_clause,[],[f2731])).

fof(f3799,plain,(
    ~ spl7_227 ),
    inference(avatar_contradiction_clause,[],[f3798])).

fof(f3798,plain,
    ( $false
    | ~ spl7_227 ),
    inference(subsumption_resolution,[],[f55,f3795])).

fof(f3795,plain,
    ( ! [X1] : ~ r1_tarski(k1_xboole_0,X1)
    | ~ spl7_227 ),
    inference(subsumption_resolution,[],[f3790,f3794])).

fof(f3794,plain,
    ( ! [X2] : ~ r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),X2)
    | ~ spl7_227 ),
    inference(forward_demodulation,[],[f3791,f84])).

fof(f84,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3791,plain,
    ( ! [X2] : ~ r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k6_subset_1(X2,k1_xboole_0))
    | ~ spl7_227 ),
    inference(resolution,[],[f3706,f97])).

fof(f3706,plain,
    ( r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0)
    | ~ spl7_227 ),
    inference(avatar_component_clause,[],[f3705])).

fof(f3705,plain,
    ( spl7_227
  <=> r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_227])])).

fof(f3790,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),X1)
        | ~ r1_tarski(k1_xboole_0,X1) )
    | ~ spl7_227 ),
    inference(resolution,[],[f3706,f66])).

fof(f3707,plain,
    ( spl7_227
    | spl7_224 ),
    inference(avatar_split_clause,[],[f3702,f3685,f3705])).

fof(f3685,plain,
    ( spl7_224
  <=> r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f3702,plain,
    ( r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0)
    | spl7_224 ),
    inference(resolution,[],[f3686,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK2(k1_relat_1(X0),X1),sK5(X0,sK2(k1_relat_1(X0),X1))),X0) ) ),
    inference(resolution,[],[f95,f67])).

fof(f95,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f3686,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl7_224 ),
    inference(avatar_component_clause,[],[f3685])).

fof(f3691,plain,
    ( ~ spl7_224
    | spl7_172 ),
    inference(avatar_split_clause,[],[f3690,f2596,f3685])).

fof(f2596,plain,
    ( spl7_172
  <=> r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f3690,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl7_172 ),
    inference(forward_demodulation,[],[f3642,f3443])).

fof(f3642,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)))
    | spl7_172 ),
    inference(superposition,[],[f2597,f3443])).

fof(f2597,plain,
    ( ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)))
    | spl7_172 ),
    inference(avatar_component_clause,[],[f2596])).

fof(f2733,plain,
    ( ~ spl7_3
    | spl7_189
    | ~ spl7_190
    | ~ spl7_173 ),
    inference(avatar_split_clause,[],[f2700,f2599,f2731,f2728,f108])).

fof(f2700,plain,
    ( ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_173 ),
    inference(superposition,[],[f137,f2600])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(X0)),k2_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f85,f57])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f76,f62])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2601,plain,
    ( ~ spl7_172
    | spl7_173
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f2463,f108,f2599,f2596])).

fof(f2463,plain,
    ( k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f1821,f109])).

fof(f1821,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k6_subset_1(X0,sK1)) = k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1))
        | ~ r1_tarski(k1_relat_1(k6_subset_1(X0,sK1)),k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f251,f109])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k1_relat_1(X1),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f58,f65])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f2355,plain,
    ( ~ spl7_4
    | ~ spl7_3
    | ~ spl7_2
    | spl7_135 ),
    inference(avatar_split_clause,[],[f2353,f2250,f104,f108,f112])).

fof(f2353,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl7_135 ),
    inference(resolution,[],[f2251,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2251,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl7_135 ),
    inference(avatar_component_clause,[],[f2250])).

fof(f114,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f51,f112])).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f110,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f52,f108])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f53,f104])).

fof(f53,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:31:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (21853)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (21838)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (21846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (21846)Refutation not found, incomplete strategy% (21846)------------------------------
% 0.21/0.51  % (21846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21846)Memory used [KB]: 10618
% 0.21/0.51  % (21846)Time elapsed: 0.102 s
% 0.21/0.51  % (21846)------------------------------
% 0.21/0.51  % (21846)------------------------------
% 0.21/0.52  % (21847)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21847)Refutation not found, incomplete strategy% (21847)------------------------------
% 0.21/0.52  % (21847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21840)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21839)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21847)Memory used [KB]: 10618
% 0.21/0.53  % (21847)Time elapsed: 0.091 s
% 0.21/0.53  % (21847)------------------------------
% 0.21/0.53  % (21847)------------------------------
% 0.21/0.53  % (21841)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (21854)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (21836)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21848)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (21859)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21849)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (21851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (21842)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (21860)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21837)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (21864)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21862)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21843)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (21855)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (21865)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (21845)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (21852)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (21863)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21861)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (21844)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (21857)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (21850)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (21858)Refutation not found, incomplete strategy% (21858)------------------------------
% 0.21/0.56  % (21858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21856)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (21858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21858)Memory used [KB]: 10746
% 0.21/0.57  % (21858)Time elapsed: 0.140 s
% 0.21/0.57  % (21858)------------------------------
% 0.21/0.57  % (21858)------------------------------
% 1.87/0.62  % (21945)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.64  % (21952)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.71  % (21972)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.20/0.83  % (21841)Time limit reached!
% 3.20/0.83  % (21841)------------------------------
% 3.20/0.83  % (21841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.83  % (21841)Termination reason: Time limit
% 3.20/0.83  
% 3.20/0.83  % (21841)Memory used [KB]: 9210
% 3.20/0.83  % (21841)Time elapsed: 0.408 s
% 3.20/0.83  % (21841)------------------------------
% 3.20/0.83  % (21841)------------------------------
% 4.22/0.92  % (21853)Time limit reached!
% 4.22/0.92  % (21853)------------------------------
% 4.22/0.92  % (21853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.92  % (21853)Termination reason: Time limit
% 4.22/0.92  
% 4.22/0.92  % (21853)Memory used [KB]: 13176
% 4.22/0.92  % (21853)Time elapsed: 0.511 s
% 4.22/0.92  % (21853)------------------------------
% 4.22/0.92  % (21853)------------------------------
% 4.22/0.92  % (21836)Time limit reached!
% 4.22/0.92  % (21836)------------------------------
% 4.22/0.92  % (21836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.93  % (21836)Termination reason: Time limit
% 4.36/0.93  % (21836)Termination phase: Saturation
% 4.36/0.93  
% 4.36/0.93  % (21836)Memory used [KB]: 5117
% 4.36/0.93  % (21836)Time elapsed: 0.500 s
% 4.36/0.93  % (21836)------------------------------
% 4.36/0.93  % (21836)------------------------------
% 4.36/0.94  % (21848)Time limit reached!
% 4.36/0.94  % (21848)------------------------------
% 4.36/0.94  % (21848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.95  % (21848)Termination reason: Time limit
% 4.36/0.95  
% 4.36/0.95  % (21848)Memory used [KB]: 8059
% 4.36/0.95  % (21848)Time elapsed: 0.525 s
% 4.36/0.95  % (21848)------------------------------
% 4.36/0.95  % (21848)------------------------------
% 4.36/0.95  % (21837)Time limit reached!
% 4.36/0.95  % (21837)------------------------------
% 4.36/0.95  % (21837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.95  % (21837)Termination reason: Time limit
% 4.36/0.95  
% 4.36/0.95  % (21837)Memory used [KB]: 8187
% 4.36/0.95  % (21837)Time elapsed: 0.525 s
% 4.36/0.95  % (21837)------------------------------
% 4.36/0.95  % (21837)------------------------------
% 4.36/0.96  % (22056)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.97/1.02  % (21852)Time limit reached!
% 4.97/1.02  % (21852)------------------------------
% 4.97/1.02  % (21852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.03  % (21852)Termination reason: Time limit
% 4.97/1.03  % (21852)Termination phase: Saturation
% 4.97/1.03  
% 4.97/1.03  % (21852)Memory used [KB]: 15991
% 4.97/1.03  % (21852)Time elapsed: 0.600 s
% 4.97/1.03  % (21852)------------------------------
% 4.97/1.03  % (21852)------------------------------
% 4.97/1.04  % (21864)Time limit reached!
% 4.97/1.04  % (21864)------------------------------
% 4.97/1.04  % (21864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.05  % (22061)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.97/1.05  % (22058)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.97/1.06  % (22059)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.97/1.06  % (21864)Termination reason: Time limit
% 4.97/1.06  
% 4.97/1.06  % (21864)Memory used [KB]: 9338
% 4.97/1.06  % (21864)Time elapsed: 0.622 s
% 4.97/1.06  % (21864)------------------------------
% 4.97/1.06  % (21864)------------------------------
% 4.97/1.07  % (21843)Time limit reached!
% 4.97/1.07  % (21843)------------------------------
% 4.97/1.07  % (21843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.07  % (21843)Termination reason: Time limit
% 4.97/1.07  
% 4.97/1.07  % (21843)Memory used [KB]: 10106
% 4.97/1.07  % (21843)Time elapsed: 0.620 s
% 4.97/1.07  % (21843)------------------------------
% 4.97/1.07  % (21843)------------------------------
% 4.97/1.07  % (22060)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.35/1.18  % (22062)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.35/1.19  % (22063)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.47/1.20  % (22064)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.47/1.21  % (21857)Time limit reached!
% 6.47/1.21  % (21857)------------------------------
% 6.47/1.21  % (21857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.47/1.22  % (21857)Termination reason: Time limit
% 6.47/1.22  
% 6.47/1.22  % (21857)Memory used [KB]: 4477
% 6.47/1.22  % (21857)Time elapsed: 0.803 s
% 6.47/1.22  % (21857)------------------------------
% 6.47/1.22  % (21857)------------------------------
% 6.73/1.28  % (22056)Time limit reached!
% 6.73/1.28  % (22056)------------------------------
% 6.73/1.28  % (22056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.73/1.30  % (22056)Termination reason: Time limit
% 6.73/1.30  
% 6.73/1.30  % (22056)Memory used [KB]: 6780
% 6.73/1.30  % (22056)Time elapsed: 0.433 s
% 6.73/1.30  % (22056)------------------------------
% 6.73/1.30  % (22056)------------------------------
% 7.36/1.36  % (22065)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.85/1.37  % (22058)Time limit reached!
% 7.85/1.37  % (22058)------------------------------
% 7.85/1.37  % (22058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.85/1.39  % (22058)Termination reason: Time limit
% 7.85/1.39  
% 7.85/1.39  % (22058)Memory used [KB]: 13432
% 7.85/1.39  % (22058)Time elapsed: 0.421 s
% 7.85/1.39  % (22058)------------------------------
% 7.85/1.39  % (22058)------------------------------
% 7.85/1.40  % (22066)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.85/1.41  % (21838)Time limit reached!
% 7.85/1.41  % (21838)------------------------------
% 7.85/1.41  % (21838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.85/1.41  % (21838)Termination reason: Time limit
% 7.85/1.41  % (21838)Termination phase: Saturation
% 7.85/1.41  
% 7.85/1.41  % (21838)Memory used [KB]: 15863
% 7.85/1.41  % (21838)Time elapsed: 1.0000 s
% 7.85/1.41  % (21838)------------------------------
% 7.85/1.41  % (21838)------------------------------
% 8.72/1.51  % (22067)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.99/1.54  % (22068)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.36/1.69  % (21862)Time limit reached!
% 10.36/1.69  % (21862)------------------------------
% 10.36/1.69  % (21862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.36/1.69  % (21862)Termination reason: Time limit
% 10.36/1.69  
% 10.36/1.69  % (21862)Memory used [KB]: 27504
% 10.36/1.69  % (21862)Time elapsed: 1.232 s
% 10.36/1.69  % (21862)------------------------------
% 10.36/1.69  % (21862)------------------------------
% 10.36/1.76  % (21860)Time limit reached!
% 10.36/1.76  % (21860)------------------------------
% 10.36/1.76  % (21860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.36/1.76  % (21860)Termination reason: Time limit
% 10.36/1.76  % (21860)Termination phase: Saturation
% 10.36/1.76  
% 10.36/1.76  % (21860)Memory used [KB]: 26609
% 10.36/1.76  % (21860)Time elapsed: 1.300 s
% 10.36/1.76  % (21860)------------------------------
% 10.36/1.76  % (21860)------------------------------
% 10.36/1.76  % (21851)Time limit reached!
% 10.36/1.76  % (21851)------------------------------
% 10.36/1.76  % (21851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.36/1.76  % (21851)Termination reason: Time limit
% 10.36/1.76  % (21851)Termination phase: Saturation
% 10.36/1.76  
% 10.36/1.76  % (21851)Memory used [KB]: 18038
% 10.36/1.76  % (21851)Time elapsed: 1.300 s
% 10.36/1.76  % (21851)------------------------------
% 10.36/1.76  % (21851)------------------------------
% 11.44/1.83  % (22066)Time limit reached!
% 11.44/1.83  % (22066)------------------------------
% 11.44/1.83  % (22066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.44/1.83  % (22066)Termination reason: Time limit
% 11.44/1.83  
% 11.44/1.83  % (22066)Memory used [KB]: 2686
% 11.44/1.83  % (22066)Time elapsed: 0.506 s
% 11.44/1.83  % (22066)------------------------------
% 11.44/1.83  % (22066)------------------------------
% 11.44/1.83  % (22069)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.44/1.85  % (22070)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.44/1.87  % (22071)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.08/1.93  % (21840)Time limit reached!
% 12.08/1.93  % (21840)------------------------------
% 12.08/1.93  % (21840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.93  % (21840)Termination reason: Time limit
% 12.08/1.93  
% 12.08/1.93  % (21840)Memory used [KB]: 18038
% 12.08/1.93  % (21840)Time elapsed: 1.509 s
% 12.08/1.93  % (21840)------------------------------
% 12.08/1.93  % (21840)------------------------------
% 12.08/1.99  % (22072)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.08/1.99  % (21863)Time limit reached!
% 12.08/1.99  % (21863)------------------------------
% 12.08/1.99  % (21863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.99  % (21863)Termination reason: Time limit
% 12.08/1.99  
% 12.08/1.99  % (21863)Memory used [KB]: 13176
% 12.08/1.99  % (21863)Time elapsed: 1.543 s
% 12.08/1.99  % (21863)------------------------------
% 12.08/1.99  % (21863)------------------------------
% 12.59/2.00  % (21855)Refutation found. Thanks to Tanya!
% 12.59/2.00  % SZS status Theorem for theBenchmark
% 12.59/2.00  % SZS output start Proof for theBenchmark
% 12.59/2.01  fof(f13419,plain,(
% 12.59/2.01    $false),
% 12.59/2.01    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f2355,f2601,f2733,f3691,f3707,f3799,f3826,f3856,f3861,f3940,f13299,f13319,f13384,f13409,f13418])).
% 12.59/2.01  fof(f13418,plain,(
% 12.59/2.01    spl7_148 | ~spl7_556),
% 12.59/2.01    inference(avatar_split_clause,[],[f13414,f13407,f2410])).
% 12.59/2.01  fof(f2410,plain,(
% 12.59/2.01    spl7_148 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).
% 12.59/2.01  fof(f13407,plain,(
% 12.59/2.01    spl7_556 <=> r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_556])])).
% 12.59/2.01  fof(f13414,plain,(
% 12.59/2.01    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~spl7_556),
% 12.59/2.01    inference(resolution,[],[f13408,f68])).
% 12.59/2.01  fof(f68,plain,(
% 12.59/2.01    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f38])).
% 12.59/2.01  fof(f38,plain,(
% 12.59/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.59/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 12.59/2.01  fof(f37,plain,(
% 12.59/2.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f36,plain,(
% 12.59/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.59/2.01    inference(rectify,[],[f35])).
% 12.59/2.01  fof(f35,plain,(
% 12.59/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.59/2.01    inference(nnf_transformation,[],[f25])).
% 12.59/2.01  fof(f25,plain,(
% 12.59/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.59/2.01    inference(ennf_transformation,[],[f1])).
% 12.59/2.01  fof(f1,axiom,(
% 12.59/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 12.59/2.01  fof(f13408,plain,(
% 12.59/2.01    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) | ~spl7_556),
% 12.59/2.01    inference(avatar_component_clause,[],[f13407])).
% 12.59/2.01  fof(f13409,plain,(
% 12.59/2.01    spl7_556 | ~spl7_189 | ~spl7_554),
% 12.59/2.01    inference(avatar_split_clause,[],[f13398,f13382,f2728,f13407])).
% 12.59/2.01  fof(f2728,plain,(
% 12.59/2.01    spl7_189 <=> r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).
% 12.59/2.01  fof(f13382,plain,(
% 12.59/2.01    spl7_554 <=> r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_554])])).
% 12.59/2.01  fof(f13398,plain,(
% 12.59/2.01    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) | (~spl7_189 | ~spl7_554)),
% 12.59/2.01    inference(resolution,[],[f13387,f2729])).
% 12.59/2.01  fof(f2729,plain,(
% 12.59/2.01    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) | ~spl7_189),
% 12.59/2.01    inference(avatar_component_clause,[],[f2728])).
% 12.59/2.01  fof(f13387,plain,(
% 12.59/2.01    ( ! [X1] : (~r1_tarski(k1_relat_1(sK1),X1) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1)) ) | ~spl7_554),
% 12.59/2.01    inference(resolution,[],[f13383,f66])).
% 12.59/2.01  fof(f66,plain,(
% 12.59/2.01    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f38])).
% 12.59/2.01  fof(f13383,plain,(
% 12.59/2.01    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1)) | ~spl7_554),
% 12.59/2.01    inference(avatar_component_clause,[],[f13382])).
% 12.59/2.01  fof(f13384,plain,(
% 12.59/2.01    ~spl7_2 | spl7_554 | ~spl7_3 | ~spl7_550),
% 12.59/2.01    inference(avatar_split_clause,[],[f13378,f13317,f108,f13382,f104])).
% 12.59/2.01  fof(f104,plain,(
% 12.59/2.01    spl7_2 <=> r1_tarski(sK0,sK1)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 12.59/2.01  fof(f108,plain,(
% 12.59/2.01    spl7_3 <=> v1_relat_1(sK1)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 12.59/2.01  fof(f13317,plain,(
% 12.59/2.01    spl7_550 <=> ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_550])])).
% 12.59/2.01  fof(f13378,plain,(
% 12.59/2.01    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | (~spl7_3 | ~spl7_550)),
% 12.59/2.01    inference(resolution,[],[f13318,f109])).
% 12.59/2.01  fof(f109,plain,(
% 12.59/2.01    v1_relat_1(sK1) | ~spl7_3),
% 12.59/2.01    inference(avatar_component_clause,[],[f108])).
% 12.59/2.01  fof(f13318,plain,(
% 12.59/2.01    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~r1_tarski(sK0,X0)) ) | ~spl7_550),
% 12.59/2.01    inference(avatar_component_clause,[],[f13317])).
% 12.59/2.01  fof(f13319,plain,(
% 12.59/2.01    ~spl7_4 | spl7_550 | spl7_148),
% 12.59/2.01    inference(avatar_split_clause,[],[f13309,f2410,f13317,f112])).
% 12.59/2.01  fof(f112,plain,(
% 12.59/2.01    spl7_4 <=> v1_relat_1(sK0)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 12.59/2.01  fof(f13309,plain,(
% 12.59/2.01    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | spl7_148),
% 12.59/2.01    inference(resolution,[],[f13302,f59])).
% 12.59/2.01  fof(f59,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f23])).
% 12.59/2.01  fof(f23,plain,(
% 12.59/2.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 12.59/2.01    inference(flattening,[],[f22])).
% 12.59/2.01  fof(f22,plain,(
% 12.59/2.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 12.59/2.01    inference(ennf_transformation,[],[f15])).
% 12.59/2.01  fof(f15,axiom,(
% 12.59/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 12.59/2.01  fof(f13302,plain,(
% 12.59/2.01    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)) ) | spl7_148),
% 12.59/2.01    inference(resolution,[],[f2411,f134])).
% 12.59/2.01  fof(f134,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2)) )),
% 12.59/2.01    inference(resolution,[],[f66,f67])).
% 12.59/2.01  fof(f67,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f38])).
% 12.59/2.01  fof(f2411,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl7_148),
% 12.59/2.01    inference(avatar_component_clause,[],[f2410])).
% 12.59/2.01  fof(f13299,plain,(
% 12.59/2.01    ~spl7_148 | ~spl7_135 | spl7_1 | ~spl7_3 | ~spl7_4),
% 12.59/2.01    inference(avatar_split_clause,[],[f13296,f112,f108,f100,f2250,f2410])).
% 12.59/2.01  fof(f2250,plain,(
% 12.59/2.01    spl7_135 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).
% 12.59/2.01  fof(f100,plain,(
% 12.59/2.01    spl7_1 <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 12.59/2.01  fof(f13296,plain,(
% 12.59/2.01    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | (~spl7_3 | ~spl7_4)),
% 12.59/2.01    inference(resolution,[],[f943,f109])).
% 12.59/2.01  fof(f943,plain,(
% 12.59/2.01    ( ! [X7] : (~v1_relat_1(X7) | r1_tarski(k3_relat_1(sK0),k3_relat_1(X7)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(X7)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(X7))) ) | ~spl7_4),
% 12.59/2.01    inference(resolution,[],[f807,f135])).
% 12.59/2.01  fof(f135,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r1_tarski(X1,k3_relat_1(X0)) | ~r1_tarski(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(superposition,[],[f75,f57])).
% 12.59/2.01  fof(f57,plain,(
% 12.59/2.01    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f20])).
% 12.59/2.01  fof(f20,plain,(
% 12.59/2.01    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 12.59/2.01    inference(ennf_transformation,[],[f13])).
% 12.59/2.01  fof(f13,axiom,(
% 12.59/2.01    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 12.59/2.01  fof(f75,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f26])).
% 12.59/2.01  fof(f26,plain,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 12.59/2.01    inference(ennf_transformation,[],[f4])).
% 12.59/2.01  fof(f4,axiom,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 12.59/2.01  fof(f807,plain,(
% 12.59/2.01    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X1) | r1_tarski(k3_relat_1(sK0),X1)) ) | ~spl7_4),
% 12.59/2.01    inference(resolution,[],[f141,f113])).
% 12.59/2.01  fof(f113,plain,(
% 12.59/2.01    v1_relat_1(sK0) | ~spl7_4),
% 12.59/2.01    inference(avatar_component_clause,[],[f112])).
% 12.59/2.01  fof(f141,plain,(
% 12.59/2.01    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | r1_tarski(k3_relat_1(X0),X1)) )),
% 12.59/2.01    inference(superposition,[],[f77,f57])).
% 12.59/2.01  fof(f77,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f29])).
% 12.59/2.01  fof(f29,plain,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 12.59/2.01    inference(flattening,[],[f28])).
% 12.59/2.01  fof(f28,plain,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 12.59/2.01    inference(ennf_transformation,[],[f8])).
% 12.59/2.01  fof(f8,axiom,(
% 12.59/2.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 12.59/2.01  fof(f3940,plain,(
% 12.59/2.01    spl7_218),
% 12.59/2.01    inference(avatar_contradiction_clause,[],[f3931])).
% 12.59/2.01  fof(f3931,plain,(
% 12.59/2.01    $false | spl7_218),
% 12.59/2.01    inference(resolution,[],[f55,f3400])).
% 12.59/2.01  fof(f3400,plain,(
% 12.59/2.01    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | spl7_218),
% 12.59/2.01    inference(avatar_component_clause,[],[f3399])).
% 12.59/2.01  fof(f3399,plain,(
% 12.59/2.01    spl7_218 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).
% 12.59/2.01  fof(f55,plain,(
% 12.59/2.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f5])).
% 12.59/2.01  fof(f5,axiom,(
% 12.59/2.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 12.59/2.01  fof(f3861,plain,(
% 12.59/2.01    ~spl7_218 | spl7_239 | ~spl7_243),
% 12.59/2.01    inference(avatar_split_clause,[],[f3860,f3854,f3824,f3399])).
% 12.59/2.01  fof(f3824,plain,(
% 12.59/2.01    spl7_239 <=> r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_239])])).
% 12.59/2.01  fof(f3854,plain,(
% 12.59/2.01    spl7_243 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_243])])).
% 12.59/2.01  fof(f3860,plain,(
% 12.59/2.01    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | (spl7_239 | ~spl7_243)),
% 12.59/2.01    inference(forward_demodulation,[],[f3825,f3855])).
% 12.59/2.01  fof(f3855,plain,(
% 12.59/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_243),
% 12.59/2.01    inference(avatar_component_clause,[],[f3854])).
% 12.59/2.01  fof(f3825,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1)) | spl7_239),
% 12.59/2.01    inference(avatar_component_clause,[],[f3824])).
% 12.59/2.01  fof(f3856,plain,(
% 12.59/2.01    spl7_243 | ~spl7_173),
% 12.59/2.01    inference(avatar_split_clause,[],[f3852,f2599,f3854])).
% 12.59/2.01  fof(f2599,plain,(
% 12.59/2.01    spl7_173 <=> k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).
% 12.59/2.01  fof(f3852,plain,(
% 12.59/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_173),
% 12.59/2.01    inference(forward_demodulation,[],[f3851,f3443])).
% 12.59/2.01  fof(f3443,plain,(
% 12.59/2.01    ( ! [X26] : (k1_xboole_0 = k6_subset_1(X26,X26)) )),
% 12.59/2.01    inference(resolution,[],[f3197,f122])).
% 12.59/2.01  fof(f122,plain,(
% 12.59/2.01    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 12.59/2.01    inference(resolution,[],[f65,f55])).
% 12.59/2.01  fof(f65,plain,(
% 12.59/2.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f34])).
% 12.59/2.01  fof(f34,plain,(
% 12.59/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.59/2.01    inference(flattening,[],[f33])).
% 12.59/2.01  fof(f33,plain,(
% 12.59/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.59/2.01    inference(nnf_transformation,[],[f3])).
% 12.59/2.01  fof(f3,axiom,(
% 12.59/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.59/2.01  fof(f3197,plain,(
% 12.59/2.01    ( ! [X4,X3] : (r1_tarski(k6_subset_1(X3,X3),X4)) )),
% 12.59/2.01    inference(duplicate_literal_removal,[],[f3190])).
% 12.59/2.01  fof(f3190,plain,(
% 12.59/2.01    ( ! [X4,X3] : (r1_tarski(k6_subset_1(X3,X3),X4) | r1_tarski(k6_subset_1(X3,X3),X4)) )),
% 12.59/2.01    inference(resolution,[],[f606,f67])).
% 12.59/2.01  fof(f606,plain,(
% 12.59/2.01    ( ! [X12,X10,X13,X11] : (~r2_hidden(sK2(k6_subset_1(X10,X11),X12),k6_subset_1(X13,X10)) | r1_tarski(k6_subset_1(X10,X11),X12)) )),
% 12.59/2.01    inference(resolution,[],[f119,f97])).
% 12.59/2.01  fof(f97,plain,(
% 12.59/2.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 12.59/2.01    inference(equality_resolution,[],[f90])).
% 12.59/2.01  fof(f90,plain,(
% 12.59/2.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 12.59/2.01    inference(definition_unfolding,[],[f79,f62])).
% 12.59/2.01  fof(f62,plain,(
% 12.59/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f9])).
% 12.59/2.01  fof(f9,axiom,(
% 12.59/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 12.59/2.01  fof(f79,plain,(
% 12.59/2.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.59/2.01    inference(cnf_transformation,[],[f50])).
% 12.59/2.01  fof(f50,plain,(
% 12.59/2.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.59/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 12.59/2.01  fof(f49,plain,(
% 12.59/2.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f48,plain,(
% 12.59/2.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.59/2.01    inference(rectify,[],[f47])).
% 12.59/2.01  fof(f47,plain,(
% 12.59/2.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.59/2.01    inference(flattening,[],[f46])).
% 12.59/2.01  fof(f46,plain,(
% 12.59/2.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.59/2.01    inference(nnf_transformation,[],[f2])).
% 12.59/2.01  fof(f2,axiom,(
% 12.59/2.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 12.59/2.01  fof(f119,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r2_hidden(sK2(k6_subset_1(X0,X1),X2),X0) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 12.59/2.01    inference(resolution,[],[f98,f67])).
% 12.59/2.01  fof(f98,plain,(
% 12.59/2.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X0)) )),
% 12.59/2.01    inference(equality_resolution,[],[f91])).
% 12.59/2.01  fof(f91,plain,(
% 12.59/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 12.59/2.01    inference(definition_unfolding,[],[f78,f62])).
% 12.59/2.01  fof(f78,plain,(
% 12.59/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.59/2.01    inference(cnf_transformation,[],[f50])).
% 12.59/2.01  fof(f3851,plain,(
% 12.59/2.01    k1_xboole_0 = k1_relat_1(k6_subset_1(sK1,sK1)) | ~spl7_173),
% 12.59/2.01    inference(forward_demodulation,[],[f2600,f3443])).
% 12.59/2.01  fof(f2600,plain,(
% 12.59/2.01    k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl7_173),
% 12.59/2.01    inference(avatar_component_clause,[],[f2599])).
% 12.59/2.01  fof(f3826,plain,(
% 12.59/2.01    ~spl7_239 | spl7_190),
% 12.59/2.01    inference(avatar_split_clause,[],[f3822,f2731,f3824])).
% 12.59/2.01  fof(f2731,plain,(
% 12.59/2.01    spl7_190 <=> r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).
% 12.59/2.01  fof(f3822,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK1)) | spl7_190),
% 12.59/2.01    inference(forward_demodulation,[],[f2732,f3443])).
% 12.59/2.01  fof(f2732,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1)) | spl7_190),
% 12.59/2.01    inference(avatar_component_clause,[],[f2731])).
% 12.59/2.01  fof(f3799,plain,(
% 12.59/2.01    ~spl7_227),
% 12.59/2.01    inference(avatar_contradiction_clause,[],[f3798])).
% 12.59/2.01  fof(f3798,plain,(
% 12.59/2.01    $false | ~spl7_227),
% 12.59/2.01    inference(subsumption_resolution,[],[f55,f3795])).
% 12.59/2.01  fof(f3795,plain,(
% 12.59/2.01    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1)) ) | ~spl7_227),
% 12.59/2.01    inference(subsumption_resolution,[],[f3790,f3794])).
% 12.59/2.01  fof(f3794,plain,(
% 12.59/2.01    ( ! [X2] : (~r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),X2)) ) | ~spl7_227),
% 12.59/2.01    inference(forward_demodulation,[],[f3791,f84])).
% 12.59/2.01  fof(f84,plain,(
% 12.59/2.01    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 12.59/2.01    inference(definition_unfolding,[],[f56,f62])).
% 12.59/2.01  fof(f56,plain,(
% 12.59/2.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.59/2.01    inference(cnf_transformation,[],[f6])).
% 12.59/2.01  fof(f6,axiom,(
% 12.59/2.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 12.59/2.01  fof(f3791,plain,(
% 12.59/2.01    ( ! [X2] : (~r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k6_subset_1(X2,k1_xboole_0))) ) | ~spl7_227),
% 12.59/2.01    inference(resolution,[],[f3706,f97])).
% 12.59/2.01  fof(f3706,plain,(
% 12.59/2.01    r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0) | ~spl7_227),
% 12.59/2.01    inference(avatar_component_clause,[],[f3705])).
% 12.59/2.01  fof(f3705,plain,(
% 12.59/2.01    spl7_227 <=> r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_227])])).
% 12.59/2.01  fof(f3790,plain,(
% 12.59/2.01    ( ! [X1] : (r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),X1) | ~r1_tarski(k1_xboole_0,X1)) ) | ~spl7_227),
% 12.59/2.01    inference(resolution,[],[f3706,f66])).
% 12.59/2.01  fof(f3707,plain,(
% 12.59/2.01    spl7_227 | spl7_224),
% 12.59/2.01    inference(avatar_split_clause,[],[f3702,f3685,f3705])).
% 12.59/2.01  fof(f3685,plain,(
% 12.59/2.01    spl7_224 <=> r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).
% 12.59/2.01  fof(f3702,plain,(
% 12.59/2.01    r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK5(k1_xboole_0,sK2(k1_relat_1(k1_xboole_0),k1_xboole_0))),k1_xboole_0) | spl7_224),
% 12.59/2.01    inference(resolution,[],[f3686,f149])).
% 12.59/2.01  fof(f149,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | r2_hidden(k4_tarski(sK2(k1_relat_1(X0),X1),sK5(X0,sK2(k1_relat_1(X0),X1))),X0)) )),
% 12.59/2.01    inference(resolution,[],[f95,f67])).
% 12.59/2.01  fof(f95,plain,(
% 12.59/2.01    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)) )),
% 12.59/2.01    inference(equality_resolution,[],[f69])).
% 12.59/2.01  fof(f69,plain,(
% 12.59/2.01    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 12.59/2.01    inference(cnf_transformation,[],[f44])).
% 12.59/2.01  fof(f44,plain,(
% 12.59/2.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 12.59/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).
% 12.59/2.01  fof(f41,plain,(
% 12.59/2.01    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f42,plain,(
% 12.59/2.01    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f43,plain,(
% 12.59/2.01    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f40,plain,(
% 12.59/2.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 12.59/2.01    inference(rectify,[],[f39])).
% 12.59/2.01  fof(f39,plain,(
% 12.59/2.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 12.59/2.01    inference(nnf_transformation,[],[f12])).
% 12.59/2.01  fof(f12,axiom,(
% 12.59/2.01    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 12.59/2.01  fof(f3686,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | spl7_224),
% 12.59/2.01    inference(avatar_component_clause,[],[f3685])).
% 12.59/2.01  fof(f3691,plain,(
% 12.59/2.01    ~spl7_224 | spl7_172),
% 12.59/2.01    inference(avatar_split_clause,[],[f3690,f2596,f3685])).
% 12.59/2.01  fof(f2596,plain,(
% 12.59/2.01    spl7_172 <=> r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)))),
% 12.59/2.01    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).
% 12.59/2.01  fof(f3690,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | spl7_172),
% 12.59/2.01    inference(forward_demodulation,[],[f3642,f3443])).
% 12.59/2.01  fof(f3642,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))) | spl7_172),
% 12.59/2.01    inference(superposition,[],[f2597,f3443])).
% 12.59/2.01  fof(f2597,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))) | spl7_172),
% 12.59/2.01    inference(avatar_component_clause,[],[f2596])).
% 12.59/2.01  fof(f2733,plain,(
% 12.59/2.01    ~spl7_3 | spl7_189 | ~spl7_190 | ~spl7_173),
% 12.59/2.01    inference(avatar_split_clause,[],[f2700,f2599,f2731,f2728,f108])).
% 12.59/2.01  fof(f2700,plain,(
% 12.59/2.01    ~r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k2_relat_1(sK1)) | r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl7_173),
% 12.59/2.01    inference(superposition,[],[f137,f2600])).
% 12.59/2.01  fof(f137,plain,(
% 12.59/2.01    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(X0)),k2_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(superposition,[],[f85,f57])).
% 12.59/2.01  fof(f85,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 12.59/2.01    inference(definition_unfolding,[],[f76,f62])).
% 12.59/2.01  fof(f76,plain,(
% 12.59/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f27])).
% 12.59/2.01  fof(f27,plain,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.59/2.01    inference(ennf_transformation,[],[f7])).
% 12.59/2.01  fof(f7,axiom,(
% 12.59/2.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 12.59/2.01  fof(f2601,plain,(
% 12.59/2.01    ~spl7_172 | spl7_173 | ~spl7_3),
% 12.59/2.01    inference(avatar_split_clause,[],[f2463,f108,f2599,f2596])).
% 12.59/2.01  fof(f2463,plain,(
% 12.59/2.01    k1_relat_1(k6_subset_1(sK1,sK1)) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k6_subset_1(sK1,sK1)),k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK1))) | ~spl7_3),
% 12.59/2.01    inference(resolution,[],[f1821,f109])).
% 12.59/2.01  fof(f1821,plain,(
% 12.59/2.01    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k6_subset_1(X0,sK1)) = k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k6_subset_1(X0,sK1)),k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)))) ) | ~spl7_3),
% 12.59/2.01    inference(resolution,[],[f251,f109])).
% 12.59/2.01  fof(f251,plain,(
% 12.59/2.01    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k1_relat_1(X1),k1_relat_1(X0)))) )),
% 12.59/2.01    inference(resolution,[],[f58,f65])).
% 12.59/2.01  fof(f58,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f21])).
% 12.59/2.01  fof(f21,plain,(
% 12.59/2.01    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 12.59/2.01    inference(ennf_transformation,[],[f14])).
% 12.59/2.01  fof(f14,axiom,(
% 12.59/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 12.59/2.01  fof(f2355,plain,(
% 12.59/2.01    ~spl7_4 | ~spl7_3 | ~spl7_2 | spl7_135),
% 12.59/2.01    inference(avatar_split_clause,[],[f2353,f2250,f104,f108,f112])).
% 12.59/2.01  fof(f2353,plain,(
% 12.59/2.01    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl7_135),
% 12.59/2.01    inference(resolution,[],[f2251,f60])).
% 12.59/2.01  fof(f60,plain,(
% 12.59/2.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 12.59/2.01    inference(cnf_transformation,[],[f23])).
% 12.59/2.01  fof(f2251,plain,(
% 12.59/2.01    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl7_135),
% 12.59/2.01    inference(avatar_component_clause,[],[f2250])).
% 12.59/2.01  fof(f114,plain,(
% 12.59/2.01    spl7_4),
% 12.59/2.01    inference(avatar_split_clause,[],[f51,f112])).
% 12.59/2.01  fof(f51,plain,(
% 12.59/2.01    v1_relat_1(sK0)),
% 12.59/2.01    inference(cnf_transformation,[],[f32])).
% 12.59/2.01  fof(f32,plain,(
% 12.59/2.01    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 12.59/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f31,f30])).
% 12.59/2.01  fof(f30,plain,(
% 12.59/2.01    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f31,plain,(
% 12.59/2.01    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 12.59/2.01    introduced(choice_axiom,[])).
% 12.59/2.01  fof(f19,plain,(
% 12.59/2.01    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 12.59/2.01    inference(flattening,[],[f18])).
% 12.59/2.01  fof(f18,plain,(
% 12.59/2.01    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 12.59/2.01    inference(ennf_transformation,[],[f17])).
% 12.59/2.01  fof(f17,negated_conjecture,(
% 12.59/2.01    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 12.59/2.01    inference(negated_conjecture,[],[f16])).
% 12.59/2.01  fof(f16,conjecture,(
% 12.59/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 12.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 12.59/2.01  fof(f110,plain,(
% 12.59/2.01    spl7_3),
% 12.59/2.01    inference(avatar_split_clause,[],[f52,f108])).
% 12.59/2.01  fof(f52,plain,(
% 12.59/2.01    v1_relat_1(sK1)),
% 12.59/2.01    inference(cnf_transformation,[],[f32])).
% 12.59/2.01  fof(f106,plain,(
% 12.59/2.01    spl7_2),
% 12.59/2.01    inference(avatar_split_clause,[],[f53,f104])).
% 12.59/2.01  fof(f53,plain,(
% 12.59/2.01    r1_tarski(sK0,sK1)),
% 12.59/2.01    inference(cnf_transformation,[],[f32])).
% 12.59/2.01  fof(f102,plain,(
% 12.59/2.01    ~spl7_1),
% 12.59/2.01    inference(avatar_split_clause,[],[f54,f100])).
% 12.59/2.01  fof(f54,plain,(
% 12.59/2.01    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 12.59/2.01    inference(cnf_transformation,[],[f32])).
% 12.59/2.01  % SZS output end Proof for theBenchmark
% 12.59/2.01  % (21855)------------------------------
% 12.59/2.01  % (21855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.59/2.01  % (21855)Termination reason: Refutation
% 12.59/2.01  
% 12.59/2.01  % (21855)Memory used [KB]: 19061
% 12.59/2.01  % (21855)Time elapsed: 1.579 s
% 12.59/2.01  % (21855)------------------------------
% 12.59/2.01  % (21855)------------------------------
% 12.59/2.01  % (21834)Success in time 1.634 s
%------------------------------------------------------------------------------
