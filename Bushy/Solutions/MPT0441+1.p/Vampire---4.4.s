%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t24_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 78.57s
% Output     : Refutation 78.57s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 327 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  437 (1692 expanded)
%              Number of equality atoms :  169 ( 957 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f271,f712,f869,f870,f1708,f1712,f1968,f3695,f3737,f4103,f4192])).

fof(f4192,plain,
    ( spl15_5
    | ~ spl15_8 ),
    inference(avatar_contradiction_clause,[],[f4191])).

fof(f4191,plain,
    ( $false
    | ~ spl15_5
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f4190,f165])).

fof(f165,plain,(
    r2_hidden(sK2,k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f154,f109])).

fof(f109,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f53,f56,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t24_relat_1.p',d4_relat_1)).

fof(f154,plain,(
    r2_hidden(k4_tarski(sK2,sK3),sK4) ),
    inference(superposition,[],[f114,f70])).

fof(f70,plain,(
    k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) = sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k2_tarski(sK1,sK3) != k2_relat_1(sK4)
      | k2_tarski(sK0,sK2) != k1_relat_1(sK4) )
    & k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) = sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( k2_tarski(X1,X3) != k2_relat_1(X4)
          | k2_tarski(X0,X2) != k1_relat_1(X4) )
        & k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 )
   => ( ( k2_tarski(sK1,sK3) != k2_relat_1(sK4)
        | k2_tarski(sK0,sK2) != k1_relat_1(sK4) )
      & k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK2,sK3)) = sK4 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) != k2_relat_1(X4)
        | k2_tarski(X0,X2) != k1_relat_1(X4) )
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( v1_relat_1(X4)
       => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
         => ( k2_tarski(X1,X3) = k2_relat_1(X4)
            & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t24_relat_1.p',t24_relat_1)).

fof(f114,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK13(X0,X1,X2) != X1
              & sK13(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( sK13(X0,X1,X2) = X1
            | sK13(X0,X1,X2) = X0
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK13(X0,X1,X2) != X1
            & sK13(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( sK13(X0,X1,X2) = X1
          | sK13(X0,X1,X2) = X0
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t24_relat_1.p',d2_tarski)).

fof(f4190,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ spl15_5
    | ~ spl15_8 ),
    inference(forward_demodulation,[],[f255,f270])).

fof(f270,plain,
    ( sK2 = sK13(sK0,sK2,k1_relat_1(sK4))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl15_8
  <=> sK2 = sK13(sK0,sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f255,plain,
    ( ~ r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl15_5
  <=> ~ r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f4103,plain,
    ( ~ spl15_14
    | spl15_17
    | spl15_19 ),
    inference(avatar_contradiction_clause,[],[f4102])).

fof(f4102,plain,
    ( $false
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_19 ),
    inference(subsumption_resolution,[],[f4086,f3228])).

fof(f3228,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK13(sK1,sK3,k2_relat_1(sK4))),sK4)
    | ~ spl15_17
    | ~ spl15_19 ),
    inference(unit_resulting_resolution,[],[f1913,f1937,f156])).

fof(f156,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK4)
      | k4_tarski(sK2,sK3) = X3
      | k4_tarski(sK0,sK1) = X3 ) ),
    inference(superposition,[],[f117,f70])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1937,plain,
    ( ! [X0,X1] : k4_tarski(X0,sK3) != k4_tarski(X1,sK13(sK1,sK3,k2_relat_1(sK4)))
    | ~ spl15_19 ),
    inference(unit_resulting_resolution,[],[f425,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t24_relat_1.p',t33_zfmisc_1)).

fof(f425,plain,
    ( sK3 != sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl15_19
  <=> sK3 != sK13(sK1,sK3,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f1913,plain,
    ( ! [X0,X1] : k4_tarski(X0,sK1) != k4_tarski(X1,sK13(sK1,sK3,k2_relat_1(sK4)))
    | ~ spl15_17 ),
    inference(unit_resulting_resolution,[],[f419,f106])).

fof(f419,plain,
    ( sK1 != sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl15_17
  <=> sK1 != sK13(sK1,sK3,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f4086,plain,
    ( r2_hidden(k4_tarski(sK12(sK4,sK13(sK1,sK3,k2_relat_1(sK4))),sK13(sK1,sK3,k2_relat_1(sK4))),sK4)
    | ~ spl15_14 ),
    inference(unit_resulting_resolution,[],[f416,f112])).

fof(f112,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK11(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t24_relat_1.p',d5_relat_1)).

fof(f416,plain,
    ( r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl15_14
  <=> r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f3737,plain,
    ( spl15_14
    | spl15_2
    | spl15_17
    | spl15_19 ),
    inference(avatar_split_clause,[],[f3736,f424,f418,f127,f415])).

fof(f127,plain,
    ( spl15_2
  <=> k2_tarski(sK1,sK3) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f3736,plain,
    ( k2_tarski(sK1,sK3) = k2_relat_1(sK4)
    | r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ spl15_17
    | ~ spl15_19 ),
    inference(subsumption_resolution,[],[f1925,f425])).

fof(f1925,plain,
    ( k2_tarski(sK1,sK3) = k2_relat_1(sK4)
    | sK3 = sK13(sK1,sK3,k2_relat_1(sK4))
    | r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ spl15_17 ),
    inference(trivial_inequality_removal,[],[f1923])).

fof(f1923,plain,
    ( sK1 != sK1
    | k2_tarski(sK1,sK3) = k2_relat_1(sK4)
    | sK3 = sK13(sK1,sK3,k2_relat_1(sK4))
    | r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ spl15_17 ),
    inference(superposition,[],[f419,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK13(X0,X1,X2) = X1
      | sK13(X0,X1,X2) = X0
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3695,plain,
    ( ~ spl15_4
    | spl15_7
    | spl15_9 ),
    inference(avatar_contradiction_clause,[],[f3694])).

fof(f3694,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_7
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f3673,f1978])).

fof(f1978,plain,
    ( ! [X0,X1] : k4_tarski(sK2,X0) != k4_tarski(sK13(sK0,sK2,k1_relat_1(sK4)),X1)
    | ~ spl15_9 ),
    inference(unit_resulting_resolution,[],[f267,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f267,plain,
    ( sK2 != sK13(sK0,sK2,k1_relat_1(sK4))
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl15_9
  <=> sK2 != sK13(sK0,sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f3673,plain,
    ( k4_tarski(sK2,sK3) = k4_tarski(sK13(sK0,sK2,k1_relat_1(sK4)),sK9(sK4,sK13(sK0,sK2,k1_relat_1(sK4))))
    | ~ spl15_4
    | ~ spl15_7 ),
    inference(unit_resulting_resolution,[],[f1892,f1954,f156])).

fof(f1954,plain,
    ( r2_hidden(k4_tarski(sK13(sK0,sK2,k1_relat_1(sK4)),sK9(sK4,sK13(sK0,sK2,k1_relat_1(sK4)))),sK4)
    | ~ spl15_4 ),
    inference(unit_resulting_resolution,[],[f258,f110])).

fof(f110,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f258,plain,
    ( r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl15_4
  <=> r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f1892,plain,
    ( ! [X0,X1] : k4_tarski(sK0,X0) != k4_tarski(sK13(sK0,sK2,k1_relat_1(sK4)),X1)
    | ~ spl15_7 ),
    inference(unit_resulting_resolution,[],[f261,f105])).

fof(f261,plain,
    ( sK0 != sK13(sK0,sK2,k1_relat_1(sK4))
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl15_7
  <=> sK0 != sK13(sK0,sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f1968,plain,
    ( ~ spl15_9
    | spl15_1
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f1963,f257,f124,f266])).

fof(f124,plain,
    ( spl15_1
  <=> k2_tarski(sK0,sK2) != k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f1963,plain,
    ( sK2 != sK13(sK0,sK2,k1_relat_1(sK4))
    | ~ spl15_1
    | ~ spl15_4 ),
    inference(unit_resulting_resolution,[],[f125,f258,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK13(X0,X1,X2) != X1
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,
    ( k2_tarski(sK0,sK2) != k1_relat_1(sK4)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1712,plain,
    ( spl15_15
    | ~ spl15_16 ),
    inference(avatar_contradiction_clause,[],[f1711])).

fof(f1711,plain,
    ( $false
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f1710,f173])).

fof(f173,plain,(
    r2_hidden(sK1,k2_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f155,f111])).

fof(f111,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f155,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK4) ),
    inference(superposition,[],[f116,f70])).

fof(f116,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1710,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK4))
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(backward_demodulation,[],[f422,f413])).

fof(f413,plain,
    ( ~ r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl15_15
  <=> ~ r2_hidden(sK13(sK1,sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f422,plain,
    ( sK1 = sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl15_16
  <=> sK1 = sK13(sK1,sK3,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f1708,plain,
    ( spl15_15
    | ~ spl15_18 ),
    inference(avatar_contradiction_clause,[],[f1707])).

fof(f1707,plain,
    ( $false
    | ~ spl15_15
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f1706,f164])).

fof(f164,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f154,f111])).

fof(f1706,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK4))
    | ~ spl15_15
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f413,f428])).

fof(f428,plain,
    ( sK3 = sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl15_18
  <=> sK3 = sK13(sK1,sK3,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f870,plain,
    ( ~ spl15_17
    | spl15_3
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f863,f415,f130,f418])).

fof(f130,plain,
    ( spl15_3
  <=> k2_tarski(sK1,sK3) != k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f863,plain,
    ( sK1 != sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_3
    | ~ spl15_14 ),
    inference(unit_resulting_resolution,[],[f131,f416,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK13(X0,X1,X2) != X0
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f131,plain,
    ( k2_tarski(sK1,sK3) != k2_relat_1(sK4)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f869,plain,
    ( ~ spl15_19
    | spl15_3
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f864,f415,f130,f424])).

fof(f864,plain,
    ( sK3 != sK13(sK1,sK3,k2_relat_1(sK4))
    | ~ spl15_3
    | ~ spl15_14 ),
    inference(unit_resulting_resolution,[],[f131,f416,f103])).

fof(f712,plain,
    ( spl15_0
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f711,f263,f121])).

fof(f121,plain,
    ( spl15_0
  <=> k2_tarski(sK0,sK2) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_0])])).

fof(f263,plain,
    ( spl15_6
  <=> sK0 = sK13(sK0,sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f711,plain,
    ( k2_tarski(sK0,sK2) = k1_relat_1(sK4)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f710,f174])).

fof(f174,plain,(
    r2_hidden(sK0,k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f155,f109])).

fof(f710,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK4))
    | k2_tarski(sK0,sK2) = k1_relat_1(sK4)
    | ~ spl15_6 ),
    inference(forward_demodulation,[],[f685,f264])).

fof(f264,plain,
    ( sK0 = sK13(sK0,sK2,k1_relat_1(sK4))
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f263])).

fof(f685,plain,
    ( k2_tarski(sK0,sK2) = k1_relat_1(sK4)
    | ~ r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | ~ spl15_6 ),
    inference(trivial_inequality_removal,[],[f681])).

fof(f681,plain,
    ( sK0 != sK0
    | k2_tarski(sK0,sK2) = k1_relat_1(sK4)
    | ~ r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | ~ spl15_6 ),
    inference(superposition,[],[f102,f264])).

fof(f271,plain,
    ( spl15_4
    | spl15_6
    | spl15_8
    | spl15_1 ),
    inference(avatar_split_clause,[],[f252,f124,f269,f263,f257])).

fof(f252,plain,
    ( sK2 = sK13(sK0,sK2,k1_relat_1(sK4))
    | sK0 = sK13(sK0,sK2,k1_relat_1(sK4))
    | r2_hidden(sK13(sK0,sK2,k1_relat_1(sK4)),k1_relat_1(sK4))
    | ~ spl15_1 ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,
    ( ! [X0] :
        ( k1_relat_1(sK4) != X0
        | sK2 = sK13(sK0,sK2,X0)
        | sK0 = sK13(sK0,sK2,X0)
        | r2_hidden(sK13(sK0,sK2,X0),X0) )
    | ~ spl15_1 ),
    inference(superposition,[],[f125,f101])).

fof(f132,plain,
    ( ~ spl15_1
    | ~ spl15_3 ),
    inference(avatar_split_clause,[],[f71,f130,f124])).

fof(f71,plain,
    ( k2_tarski(sK1,sK3) != k2_relat_1(sK4)
    | k2_tarski(sK0,sK2) != k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
