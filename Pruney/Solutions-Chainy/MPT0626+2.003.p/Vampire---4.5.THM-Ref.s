%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 385 expanded)
%              Number of leaves         :   16 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  386 (2798 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f73,f99,f101,f209,f248,f255])).

fof(f255,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f66,f253])).

fof(f253,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f252,f37])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            | ~ r2_hidden(sK0,k1_relat_1(X2))
            | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
              & r2_hidden(sK0,k1_relat_1(X2)) )
            | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
          | ~ r2_hidden(sK0,k1_relat_1(X2))
          | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            & r2_hidden(sK0,k1_relat_1(X2)) )
          | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f252,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f234,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f234,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f217,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f217,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f210,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f210,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f61,f127])).

fof(f127,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(resolution,[],[f74,f37])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f248,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f242,f70])).

fof(f70,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f242,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f218,f239])).

fof(f239,plain,
    ( k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f238,f37])).

fof(f238,plain,
    ( k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f235,f38])).

fof(f235,plain,
    ( k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f217,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f218,plain,
    ( r2_hidden(sK6(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f214,f37])).

fof(f214,plain,
    ( r2_hidden(sK6(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f210,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f209,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f204,f130])).

% (3252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f130,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | spl7_1 ),
    inference(backward_demodulation,[],[f62,f127])).

fof(f62,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f204,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X1)
        | r2_hidden(sK0,k10_relat_1(sK2,X1)) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_5
  <=> ! [X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X1)
        | r2_hidden(sK0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f101,plain,
    ( ~ spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f95,f90])).

fof(f90,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f80,f37])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f65,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f95,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_4
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f99,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f91,f64,f97,f93])).

fof(f91,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X1)
        | r2_hidden(sK0,k10_relat_1(sK2,X1))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X1)
        | r2_hidden(sK0,k10_relat_1(sK2,X1))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f39,f64,f60])).

fof(f39,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f40,f68,f60])).

fof(f40,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f41,f68,f64,f60])).

fof(f41,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:12:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (3261)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (3245)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (3250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (3251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (3241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3245)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (3242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f71,f72,f73,f99,f101,f209,f248,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~spl7_1 | spl7_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    $false | (~spl7_1 | spl7_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f66,f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f252,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f217,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK6(sK0,k1_relat_1(sK1),sK2)),sK2) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f37])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK6(sK0,k1_relat_1(sK1),sK2)),sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f210,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | ~spl7_1),
% 0.21/0.53    inference(forward_demodulation,[],[f61,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f74,f37])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 0.21/0.53    inference(resolution,[],[f35,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl7_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl7_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ~spl7_1 | spl7_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    $false | (~spl7_1 | spl7_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f242,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl7_3 <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~spl7_1),
% 0.21/0.53    inference(backward_demodulation,[],[f218,f239])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f238,f37])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f235,f38])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    k1_funct_1(sK2,sK0) = sK6(sK0,k1_relat_1(sK1),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f217,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    r2_hidden(sK6(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) | ~spl7_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f214,f37])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    r2_hidden(sK6(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f210,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    spl7_1 | ~spl7_3 | ~spl7_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    $false | (spl7_1 | ~spl7_3 | ~spl7_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f204,f130])).
% 0.21/0.53  % (3252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | spl7_1),
% 0.21/0.53    inference(backward_demodulation,[],[f62,f127])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f60])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | (~spl7_3 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f98,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f68])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(k1_funct_1(sK2,sK0),X1) | r2_hidden(sK0,k10_relat_1(sK2,X1))) ) | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl7_5 <=> ! [X1] : (~r2_hidden(k1_funct_1(sK2,sK0),X1) | r2_hidden(sK0,k10_relat_1(sK2,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl7_2 | spl7_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    $false | (~spl7_2 | spl7_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl7_2),
% 0.21/0.53    inference(resolution,[],[f81,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl7_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f80,f37])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_relat_1(sK2) | ~spl7_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f38])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_2),
% 0.21/0.54    inference(resolution,[],[f65,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl7_4 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ~spl7_4 | spl7_5 | ~spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f91,f64,f97,f93])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_funct_1(sK2,sK0),X1) | r2_hidden(sK0,k10_relat_1(sK2,X1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))) ) | ~spl7_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f37])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_funct_1(sK2,sK0),X1) | r2_hidden(sK0,k10_relat_1(sK2,X1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_2),
% 0.21/0.54    inference(resolution,[],[f81,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f64,f60])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl7_1 | spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f68,f60])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f68,f64,f60])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (3245)------------------------------
% 0.21/0.54  % (3245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3245)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (3245)Memory used [KB]: 10874
% 0.21/0.54  % (3245)Time elapsed: 0.112 s
% 0.21/0.54  % (3245)------------------------------
% 0.21/0.54  % (3245)------------------------------
% 0.21/0.54  % (3236)Success in time 0.173 s
%------------------------------------------------------------------------------
