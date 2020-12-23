%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0598+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1553,f1558,f1563,f1568,f1616])).

fof(f1616,plain,
    ( ~ spl36_1
    | ~ spl36_2
    | spl36_3
    | ~ spl36_4 ),
    inference(avatar_contradiction_clause,[],[f1615])).

fof(f1615,plain,
    ( $false
    | ~ spl36_1
    | ~ spl36_2
    | spl36_3
    | ~ spl36_4 ),
    inference(subsumption_resolution,[],[f1614,f1613])).

fof(f1613,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),sK0)
    | spl36_3
    | ~ spl36_4 ),
    inference(unit_resulting_resolution,[],[f1562,f1567,f1173])).

fof(f1173,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1060])).

fof(f1060,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1058,f1059])).

fof(f1059,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1057])).

fof(f1057,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1567,plain,
    ( r2_hidden(sK2,k2_relat_1(sK1))
    | ~ spl36_4 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1565,plain,
    ( spl36_4
  <=> r2_hidden(sK2,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_4])])).

fof(f1562,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl36_3 ),
    inference(avatar_component_clause,[],[f1560])).

fof(f1560,plain,
    ( spl36_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_3])])).

fof(f1614,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl36_1
    | ~ spl36_2 ),
    inference(unit_resulting_resolution,[],[f1552,f1557,f1194])).

fof(f1194,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f1069])).

fof(f1069,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f889])).

fof(f889,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1557,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl36_2 ),
    inference(avatar_component_clause,[],[f1555])).

fof(f1555,plain,
    ( spl36_2
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_2])])).

fof(f1552,plain,
    ( v1_relat_1(sK1)
    | ~ spl36_1 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f1550,plain,
    ( spl36_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_1])])).

fof(f1568,plain,(
    spl36_4 ),
    inference(avatar_split_clause,[],[f1169,f1565])).

fof(f1169,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1054])).

fof(f1054,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f868,f1053,f1052])).

fof(f1052,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1053,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,sK0)
        & r2_hidden(X2,k2_relat_1(sK1)) )
   => ( ~ r2_hidden(sK2,sK0)
      & r2_hidden(sK2,k2_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f868,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f867])).

fof(f867,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f797])).

fof(f797,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f796])).

fof(f796,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f1563,plain,(
    ~ spl36_3 ),
    inference(avatar_split_clause,[],[f1170,f1560])).

fof(f1170,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f1054])).

fof(f1558,plain,(
    spl36_2 ),
    inference(avatar_split_clause,[],[f1168,f1555])).

fof(f1168,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1054])).

fof(f1553,plain,(
    spl36_1 ),
    inference(avatar_split_clause,[],[f1167,f1550])).

fof(f1167,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1054])).
%------------------------------------------------------------------------------
