%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0722+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:32 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 644 expanded)
%              Number of leaves         :   15 ( 214 expanded)
%              Depth                    :   16
%              Number of atoms          :  592 (3880 expanded)
%              Number of equality atoms :  174 ( 964 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f962,f994,f999,f1348])).

fof(f1348,plain,
    ( spl7_7
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f1347])).

fof(f1347,plain,
    ( $false
    | spl7_7
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f1345,f330])).

fof(f330,plain,
    ( ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl7_7
  <=> r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1345,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f1110,f1343])).

fof(f1343,plain,
    ( sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f1342,f993])).

fof(f993,plain,
    ( sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl7_22
  <=> sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1342,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) = sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f1330,f1109])).

fof(f1109,plain,
    ( sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = k1_funct_1(sK0,sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f37,f38,f998,f81])).

fof(f81,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f998,plain,
    ( r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k9_relat_1(sK0,sK1))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f996])).

fof(f996,plain,
    ( spl7_23
  <=> r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f38,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1330,plain,
    ( sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f84,f85,f1111,f71])).

fof(f71,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f1111,plain,
    ( r2_hidden(sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k1_relat_1(sK0))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f37,f38,f998,f83])).

fof(f83,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f84,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1110,plain,
    ( r2_hidden(sK6(sK0,sK1,sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),sK1)
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f37,f38,f998,f82])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f999,plain,
    ( spl7_7
    | spl7_23 ),
    inference(avatar_split_clause,[],[f371,f996,f329])).

fof(f371,plain,
    ( r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k9_relat_1(sK0,sK1))
    | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1) ) ),
    inference(subsumption_resolution,[],[f127,f84])).

fof(f127,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f98,f85])).

fof(f98,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f41,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f994,plain,
    ( spl7_7
    | spl7_22 ),
    inference(avatar_split_clause,[],[f372,f991,f329])).

fof(f372,plain,
    ( sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))
    | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f129,f84])).

fof(f129,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f85])).

fof(f99,plain,(
    ! [X2] :
      ( sK1 != X2
      | sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2) = k1_funct_1(k2_funct_1(sK0),sK5(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2))
      | r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f41,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f962,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f943,f702])).

fof(f702,plain,
    ( sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f84,f85,f397,f71])).

fof(f397,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f40,f331,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f331,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f329])).

fof(f40,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f943,plain,
    ( sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) != k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f701,f699,f384])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) != k1_funct_1(k2_funct_1(sK0),X0)
        | ~ r2_hidden(X0,k9_relat_1(sK0,sK1)) )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f383,f331])).

fof(f383,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) != k1_funct_1(k2_funct_1(sK0),X0)
      | ~ r2_hidden(X0,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),X4) != sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3) ) ),
    inference(forward_demodulation,[],[f132,f86])).

fof(f86,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f132,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3) ) ),
    inference(subsumption_resolution,[],[f131,f84])).

fof(f131,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f100,f85])).

fof(f100,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f41,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK4(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f699,plain,
    ( r2_hidden(k1_funct_1(sK0,sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,sK1))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f37,f38,f331,f397,f80])).

fof(f80,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f701,plain,
    ( r2_hidden(k1_funct_1(sK0,sK4(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k2_relat_1(sK0))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f84,f85,f397,f73])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,k2_relat_1(X0))
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
