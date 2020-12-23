%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 221 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  521 (1042 expanded)
%              Number of equality atoms :   92 ( 213 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f140,f150,f167,f171,f186,f188,f237,f244,f266,f273,f283,f340,f349])).

fof(f349,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_xboole_0 != k1_funct_1(k5_relat_1(sK1,sK2),sK0)
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f340,plain,
    ( spl7_1
    | spl7_27
    | ~ spl7_2
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f334,f281,f69,f235,f65])).

fof(f65,plain,
    ( spl7_1
  <=> k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f235,plain,
    ( spl7_27
  <=> k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f69,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f281,plain,
    ( spl7_33
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f334,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_33 ),
    inference(resolution,[],[f282,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( ~ spl7_4
    | ~ spl7_3
    | spl7_33
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f278,f271,f281,f73,f77])).

fof(f77,plain,
    ( spl7_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f73,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f271,plain,
    ( spl7_32
  <=> ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_32 ),
    inference(resolution,[],[f272,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f272,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2)) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f271])).

fof(f273,plain,
    ( ~ spl7_6
    | ~ spl7_5
    | spl7_32
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f269,f264,f271,f81,f85])).

fof(f85,plain,
    ( spl7_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f81,plain,
    ( spl7_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f264,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f269,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_31 ),
    inference(resolution,[],[f265,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( ~ spl7_4
    | ~ spl7_3
    | spl7_31
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f262,f242,f264,f73,f77])).

fof(f242,plain,
    ( spl7_28
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(k4_tarski(X1,X2),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_28 ),
    inference(resolution,[],[f243,f62])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( ~ spl7_6
    | ~ spl7_4
    | spl7_28
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f239,f169,f242,f77,f85])).

fof(f169,plain,
    ( spl7_17
  <=> ! [X1,X2] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1))
        | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ r2_hidden(k4_tarski(X1,X2),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_17 ),
    inference(resolution,[],[f170,f90])).

fof(f90,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f57,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f170,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2))
        | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f237,plain,
    ( spl7_26
    | ~ spl7_27
    | spl7_1
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f230,f165,f65,f235,f232])).

fof(f232,plain,
    ( spl7_26
  <=> k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f165,plain,
    ( spl7_16
  <=> ! [X0] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f230,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),sK0)
    | spl7_1
    | ~ spl7_16 ),
    inference(inner_rewriting,[],[f227])).

fof(f227,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | spl7_1
    | ~ spl7_16 ),
    inference(superposition,[],[f66,f166])).

fof(f166,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0)
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f66,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f188,plain,
    ( ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_15 ),
    inference(avatar_split_clause,[],[f187,f162,f73,f77,f81,f85])).

fof(f162,plain,
    ( spl7_15
  <=> v1_funct_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f187,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_15 ),
    inference(resolution,[],[f163,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f163,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f186,plain,
    ( ~ spl7_6
    | ~ spl7_4
    | spl7_14 ),
    inference(avatar_split_clause,[],[f183,f159,f77,f85])).

fof(f159,plain,
    ( spl7_14
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f183,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl7_14 ),
    inference(resolution,[],[f160,f53])).

fof(f160,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f171,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_17
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f156,f148,f169,f162,f159])).

fof(f148,plain,
    ( spl7_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f156,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1))
        | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2))
        | ~ v1_funct_1(k5_relat_1(sK1,sK2))
        | ~ v1_relat_1(k5_relat_1(sK1,sK2)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f167,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f155,f148,f165,f162,f159])).

fof(f155,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0)
        | ~ v1_funct_1(k5_relat_1(sK1,sK2))
        | ~ v1_relat_1(k5_relat_1(sK1,sK2)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f149,f60])).

fof(f150,plain,
    ( spl7_12
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f144,f138,f73,f77,f148])).

fof(f138,plain,
    ( spl7_11
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(resolution,[],[f139,f74])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f139,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3)))
        | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( ~ spl7_6
    | spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f131,f81,f138,f85])).

fof(f131,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3)))
        | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | ~ spl7_5 ),
    inference(resolution,[],[f52,f82])).

fof(f82,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f87,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
            & r2_hidden(X0,k1_relat_1(X1))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0))
          & r2_hidden(sK0,k1_relat_1(sK1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0))
        & r2_hidden(sK0,k1_relat_1(sK1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
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
           => ( r2_hidden(X0,k1_relat_1(X1))
             => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f83,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f39,f65])).

fof(f39,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (8220)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.45  % (8212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (8217)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (8219)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (8221)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (8213)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (8212)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f350,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f140,f150,f167,f171,f186,f188,f237,f244,f266,f273,f283,f340,f349])).
% 0.21/0.47  fof(f349,plain,(
% 0.21/0.47    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | k1_xboole_0 != k1_funct_1(k5_relat_1(sK1,sK2),sK0) | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f340,plain,(
% 0.21/0.47    spl7_1 | spl7_27 | ~spl7_2 | ~spl7_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f334,f281,f69,f235,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl7_1 <=> k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    spl7_27 <=> k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl7_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    spl7_33 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.47  fof(f334,plain,(
% 0.21/0.47    k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | (~spl7_2 | ~spl7_33)),
% 0.21/0.47    inference(resolution,[],[f282,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl7_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f281])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    ~spl7_4 | ~spl7_3 | spl7_33 | ~spl7_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f278,f271,f281,f73,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl7_4 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl7_3 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    spl7_32 <=> ! [X2] : (~r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.47  fof(f278,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_32),
% 0.21/0.47    inference(resolution,[],[f272,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    ( ! [X2] : (~r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2))) ) | ~spl7_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f271])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~spl7_6 | ~spl7_5 | spl7_32 | ~spl7_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f269,f264,f271,f81,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl7_6 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl7_5 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    spl7_31 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    ( ! [X2] : (~r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK1,sK2),X2) = k1_funct_1(sK2,k1_funct_1(sK1,X2)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl7_31),
% 0.21/0.47    inference(resolution,[],[f265,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl7_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f264])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    ~spl7_4 | ~spl7_3 | spl7_31 | ~spl7_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f262,f242,f264,f73,f77])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    spl7_28 <=> ! [X1,X0,X2] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(k4_tarski(X1,X2),sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_28),
% 0.21/0.47    inference(resolution,[],[f243,f62])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl7_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f242])).
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    ~spl7_6 | ~spl7_4 | spl7_28 | ~spl7_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f239,f169,f242,f77,f85])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    spl7_17 <=> ! [X1,X2] : (k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1)) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(k4_tarski(X1,X2),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)) ) | ~spl7_17),
% 0.21/0.47    inference(resolution,[],[f170,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2)) | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1))) ) | ~spl7_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f169])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    spl7_26 | ~spl7_27 | spl7_1 | ~spl7_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f230,f165,f65,f235,f232])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    spl7_26 <=> k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl7_16 <=> ! [X0] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),sK0) | (spl7_1 | ~spl7_16)),
% 0.21/0.47    inference(inner_rewriting,[],[f227])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | (spl7_1 | ~spl7_16)),
% 0.21/0.47    inference(superposition,[],[f66,f166])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl7_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f165])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | spl7_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~spl7_6 | ~spl7_5 | ~spl7_4 | ~spl7_3 | spl7_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f187,f162,f73,f77,f81,f85])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl7_15 <=> v1_funct_1(k5_relat_1(sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_15),
% 0.21/0.47    inference(resolution,[],[f163,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~v1_funct_1(k5_relat_1(sK1,sK2)) | spl7_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f162])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ~spl7_6 | ~spl7_4 | spl7_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f183,f159,f77,f85])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl7_14 <=> v1_relat_1(k5_relat_1(sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | spl7_14),
% 0.21/0.47    inference(resolution,[],[f160,f53])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ~v1_relat_1(k5_relat_1(sK1,sK2)) | spl7_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f159])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ~spl7_14 | ~spl7_15 | spl7_17 | ~spl7_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f156,f148,f169,f162,f159])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl7_12 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2))) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1)) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK1,sK2)) | ~v1_funct_1(k5_relat_1(sK1,sK2)) | ~v1_relat_1(k5_relat_1(sK1,sK2))) ) | ~spl7_12),
% 0.21/0.47    inference(resolution,[],[f149,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2))) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl7_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~spl7_14 | ~spl7_15 | spl7_16 | ~spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f148,f165,f162,f159])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | k1_xboole_0 = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~v1_funct_1(k5_relat_1(sK1,sK2)) | ~v1_relat_1(k5_relat_1(sK1,sK2))) ) | ~spl7_12),
% 0.21/0.48    inference(resolution,[],[f149,f60])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl7_12 | ~spl7_4 | ~spl7_3 | ~spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f144,f138,f73,f77,f148])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl7_11 <=> ! [X3,X2] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3))) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2))) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | (~spl7_3 | ~spl7_11)),
% 0.21/0.48    inference(resolution,[],[f139,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~v1_funct_1(X3) | ~v1_relat_1(X3) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3))) | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2))) ) | ~spl7_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f138])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~spl7_6 | spl7_11 | ~spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f131,f81,f138,f85])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,X3))) | k1_funct_1(k5_relat_1(sK1,X3),X2) = k1_funct_1(X3,k1_funct_1(sK1,X2)) | ~v1_relat_1(sK1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | ~spl7_5),
% 0.21/0.48    inference(resolution,[],[f52,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    v1_funct_1(sK1) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f85])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    (k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X2] : (k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f73])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f69])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl7_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f65])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (8212)------------------------------
% 0.21/0.48  % (8212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8212)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (8212)Memory used [KB]: 10874
% 0.21/0.48  % (8212)Time elapsed: 0.059 s
% 0.21/0.48  % (8212)------------------------------
% 0.21/0.48  % (8212)------------------------------
% 0.21/0.48  % (8211)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8205)Success in time 0.128 s
%------------------------------------------------------------------------------
