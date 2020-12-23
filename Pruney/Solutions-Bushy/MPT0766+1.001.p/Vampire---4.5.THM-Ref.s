%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0766+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 401 expanded)
%              Number of leaves         :   16 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  365 (3271 expanded)
%              Number of equality atoms :   40 ( 314 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f109,f133])).

fof(f133,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f124,f37])).

fof(f37,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
          & sK1 != sK2(X2)
          & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
          & r2_hidden(sK2(X2),k3_relat_1(sK0)) )
        | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
        | ~ r2_hidden(X2,k3_relat_1(sK0)) )
    & ~ r2_hidden(k4_tarski(sK3,sK1),sK0)
    & r2_hidden(sK3,k3_relat_1(sK0))
    & r2_hidden(sK1,k3_relat_1(sK0))
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & X1 != X3
                    & r2_hidden(k4_tarski(X1,X3),X0)
                    & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X1,X2),X0)
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & ? [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                & r2_hidden(X4,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK0)
                  & r2_hidden(X3,k3_relat_1(sK0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK0)
              | ~ r2_hidden(X2,k3_relat_1(sK0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK0)
              & r2_hidden(X4,k3_relat_1(sK0)) )
          & r2_hidden(X1,k3_relat_1(sK0)) )
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                & X1 != X3
                & r2_hidden(k4_tarski(X1,X3),sK0)
                & r2_hidden(X3,k3_relat_1(sK0)) )
            | ~ r2_hidden(k4_tarski(X1,X2),sK0)
            | ~ r2_hidden(X2,k3_relat_1(sK0)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),sK0)
            & r2_hidden(X4,k3_relat_1(sK0)) )
        & r2_hidden(X1,k3_relat_1(sK0)) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
              & sK1 != X3
              & r2_hidden(k4_tarski(sK1,X3),sK0)
              & r2_hidden(X3,k3_relat_1(sK0)) )
          | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
          | ~ r2_hidden(X2,k3_relat_1(sK0)) )
      & ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK1),sK0)
          & r2_hidden(X4,k3_relat_1(sK0)) )
      & r2_hidden(sK1,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
          & sK1 != X3
          & r2_hidden(k4_tarski(sK1,X3),sK0)
          & r2_hidden(X3,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
        & sK1 != sK2(X2)
        & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
        & r2_hidden(sK2(X2),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK1),sK0)
        & r2_hidden(X4,k3_relat_1(sK0)) )
   => ( ~ r2_hidden(k4_tarski(sK3,sK1),sK0)
      & r2_hidden(sK3,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).

fof(f124,plain,
    ( ~ r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f123,f38])).

fof(f38,plain,(
    ~ r2_hidden(k4_tarski(sK3,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f123,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK1),sK0)
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f119,plain,
    ( ! [X1] :
        ( r2_hidden(X1,o_0_0_xboole_0)
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,sK1),sK0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f76,f106])).

fof(f106,plain,
    ( o_0_0_xboole_0 = sK5(sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_2
  <=> o_0_0_xboole_0 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK5(sK0,X1))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(X3,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK5(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK5(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK5(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK5(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f109,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f108,f104,f100])).

fof(f100,plain,
    ( spl7_1
  <=> r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f108,plain,
    ( o_0_0_xboole_0 = sK5(sK0,sK1)
    | r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f36,plain,(
    r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | o_0_0_xboole_0 = sK5(sK0,sK1)
    | r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | o_0_0_xboole_0 = sK5(sK0,sK1)
    | r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0)
    | ~ r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,X0),sK0)
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | o_0_0_xboole_0 = sK5(sK0,X0) ) ),
    inference(resolution,[],[f89,f76])).

fof(f89,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK5(sK0,X2))
      | o_0_0_xboole_0 = sK5(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f88,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(sK5(sK0,X0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(sK5(sK0,X0),k3_relat_1(sK0))
      | r1_tarski(sK5(sK0,X0),k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,k3_relat_1(sK0)),sK5(sK0,X1))
      | r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_relat_1(sK0))
      | ~ r2_hidden(X0,sK5(sK0,X1)) ) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK5(X0,X1))
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK5(sK0,X2),k3_relat_1(sK0))
      | ~ r2_hidden(X2,sK5(sK0,X2))
      | o_0_0_xboole_0 = sK5(sK0,X2) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK5(sK0,X2),k3_relat_1(sK0))
      | ~ r2_hidden(X2,sK5(sK0,X2))
      | o_0_0_xboole_0 = sK5(sK0,X2)
      | ~ r1_tarski(sK5(sK0,X2),k3_relat_1(sK0))
      | o_0_0_xboole_0 = sK5(sK0,X2) ) ),
    inference(resolution,[],[f85,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0),X0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | r2_hidden(sK4(sK0,X0),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK4(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0),sK5(sK0,X1))
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ r2_hidden(X1,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X0,sK5(sK0,X1)) ) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK5(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(sK0,X1),X0),sK0)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f83,f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(sK4(sK0,X1),X0),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X3,X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f98,f104,f100])).

fof(f98,plain,
    ( o_0_0_xboole_0 = sK5(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f97,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | o_0_0_xboole_0 = sK5(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK0))
    | o_0_0_xboole_0 = sK5(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK1,sK2(sK1)),sK0)
    | ~ r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
