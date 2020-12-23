%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0723+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 156 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  265 ( 995 expanded)
%              Number of equality atoms :  110 ( 577 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2065,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f1969,f2005,f2013,f2020,f2064])).

fof(f2064,plain,(
    spl5_161 ),
    inference(avatar_contradiction_clause,[],[f2063])).

fof(f2063,plain,
    ( $false
    | spl5_161 ),
    inference(resolution,[],[f2019,f31])).

fof(f31,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f2019,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK2,sK0,sK1))
    | spl5_161 ),
    inference(avatar_component_clause,[],[f2018])).

fof(f2018,plain,
    ( spl5_161
  <=> r2_hidden(sK1,k1_enumset1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f2020,plain,
    ( ~ spl5_161
    | ~ spl5_2
    | ~ spl5_160 ),
    inference(avatar_split_clause,[],[f2014,f2003,f42,f2018])).

fof(f42,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2003,plain,
    ( spl5_160
  <=> ! [X14] :
        ( ~ r2_hidden(X14,sK2)
        | ~ r2_hidden(X14,k1_enumset1(sK2,sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f2014,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK2,sK0,sK1))
    | ~ spl5_2
    | ~ spl5_160 ),
    inference(resolution,[],[f2004,f43])).

fof(f43,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f2004,plain,
    ( ! [X14] :
        ( ~ r2_hidden(X14,sK2)
        | ~ r2_hidden(X14,k1_enumset1(sK2,sK0,sK1)) )
    | ~ spl5_160 ),
    inference(avatar_component_clause,[],[f2003])).

fof(f2013,plain,(
    ~ spl5_155 ),
    inference(avatar_contradiction_clause,[],[f2006])).

fof(f2006,plain,
    ( $false
    | ~ spl5_155 ),
    inference(resolution,[],[f1968,f31])).

fof(f1968,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_enumset1(sK2,sK0,sK1))
    | ~ spl5_155 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f1967,plain,
    ( spl5_155
  <=> ! [X0] : ~ r2_hidden(X0,k1_enumset1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f2005,plain,
    ( spl5_155
    | spl5_160
    | ~ spl5_154 ),
    inference(avatar_split_clause,[],[f1984,f1964,f2003,f1967])).

fof(f1964,plain,
    ( spl5_154
  <=> sK2 = sK3(k1_enumset1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f1984,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(X14,sK2)
        | ~ r2_hidden(X14,k1_enumset1(sK2,sK0,sK1))
        | ~ r2_hidden(X15,k1_enumset1(sK2,sK0,sK1)) )
    | ~ spl5_154 ),
    inference(superposition,[],[f21,f1965])).

fof(f1965,plain,
    ( sK2 = sK3(k1_enumset1(sK2,sK0,sK1))
    | ~ spl5_154 ),
    inference(avatar_component_clause,[],[f1964])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f10])).

fof(f10,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f1969,plain,
    ( spl5_154
    | spl5_155
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1962,f46,f38,f1967,f1964])).

fof(f38,plain,
    ( spl5_1
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f46,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1962,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_enumset1(sK2,sK0,sK1))
        | sK2 = sK3(k1_enumset1(sK2,sK0,sK1)) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f1959,f35])).

fof(f35,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1959,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,k1_enumset1(X0,sK0,sK1))
        | ~ r2_hidden(X1,k1_enumset1(X0,sK0,sK1))
        | sK3(k1_enumset1(X0,sK0,sK1)) = X0 )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f1397,f39])).

fof(f39,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f1397,plain,
    ( ! [X26,X27,X25] :
        ( ~ r2_hidden(X26,sK0)
        | ~ r2_hidden(X26,k1_enumset1(X25,sK0,sK1))
        | ~ r2_hidden(X27,k1_enumset1(X25,sK0,sK1))
        | sK3(k1_enumset1(X25,sK0,sK1)) = X25 )
    | ~ spl5_3 ),
    inference(superposition,[],[f21,f1380])).

fof(f1380,plain,
    ( ! [X12] :
        ( sK0 = sK3(k1_enumset1(X12,sK0,sK1))
        | sK3(k1_enumset1(X12,sK0,sK1)) = X12 )
    | ~ spl5_3 ),
    inference(resolution,[],[f1341,f47])).

fof(f47,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f1341,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | sK3(k1_enumset1(X0,X1,X2)) = X1
      | sK3(k1_enumset1(X0,X1,X2)) = X0 ) ),
    inference(resolution,[],[f1160,f31])).

fof(f1160,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k1_enumset1(X5,X6,X7))
      | sK3(k1_enumset1(X5,X6,X7)) = X5
      | sK3(k1_enumset1(X5,X6,X7)) = X6
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f448,f33])).

fof(f33,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f448,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
      | ~ r2_hidden(X4,k1_enumset1(X1,X2,X3))
      | sK3(k1_enumset1(X1,X2,X3)) = X1
      | sK3(k1_enumset1(X1,X2,X3)) = X2
      | ~ r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f58,f31])).

fof(f58,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r2_hidden(X11,k1_enumset1(X6,X7,X8))
      | ~ r2_hidden(X9,k1_enumset1(X6,X7,X8))
      | ~ r2_hidden(X10,k1_enumset1(X6,X7,X8))
      | sK3(k1_enumset1(X6,X7,X8)) = X6
      | sK3(k1_enumset1(X6,X7,X8)) = X7
      | ~ r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f21,f56])).

fof(f56,plain,(
    ! [X12,X10,X11,X9] :
      ( sK3(k1_enumset1(X10,X9,X11)) = X11
      | sK3(k1_enumset1(X10,X9,X11)) = X10
      | sK3(k1_enumset1(X10,X9,X11)) = X9
      | ~ r2_hidden(X12,k1_enumset1(X10,X9,X11)) ) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( r2_hidden(sK2,sK0)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK2,sK0)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X2,X0)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X2,X0)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f44,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
