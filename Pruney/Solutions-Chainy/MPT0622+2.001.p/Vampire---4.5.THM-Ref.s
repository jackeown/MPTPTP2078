%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 443 expanded)
%              Number of leaves         :   24 ( 141 expanded)
%              Depth                    :   26
%              Number of atoms          :  727 (2400 expanded)
%              Number of equality atoms :  135 ( 650 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f555,f562,f594,f601])).

fof(f601,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | spl9_17
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_8
    | spl9_17
    | spl9_18 ),
    inference(subsumption_resolution,[],[f599,f112])).

fof(f112,plain,
    ( v1_funct_1(sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_7
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f599,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl9_8
    | spl9_17
    | spl9_18 ),
    inference(subsumption_resolution,[],[f598,f561])).

fof(f561,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl9_17
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f598,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ spl9_8
    | spl9_18 ),
    inference(subsumption_resolution,[],[f596,f117])).

fof(f117,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl9_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f596,plain,
    ( ~ v1_relat_1(sK1)
    | r1_tarski(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | spl9_18 ),
    inference(resolution,[],[f593,f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(X2,X3),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK7(X2,X3),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f593,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1))
    | spl9_18 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl9_18
  <=> r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f594,plain,
    ( ~ spl9_18
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_17 ),
    inference(avatar_split_clause,[],[f589,f559,f115,f110,f105,f100,f95,f90,f85,f591])).

fof(f85,plain,
    ( spl9_2
  <=> k1_tarski(sK0) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f90,plain,
    ( spl9_3
  <=> k1_tarski(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f95,plain,
    ( spl9_4
  <=> k1_relat_1(sK1) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f100,plain,
    ( spl9_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f105,plain,
    ( spl9_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f589,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_17 ),
    inference(subsumption_resolution,[],[f588,f561])).

fof(f588,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f544,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f180,f97])).

fof(f97,plain,
    ( k1_relat_1(sK1) = k1_relat_1(sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f180,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f179,f107])).

fof(f107,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f179,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f173,f102])).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f173,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f76,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( sK0 = k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f138,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f137,f97])).

fof(f137,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f136,f107])).

fof(f136,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f134,f102])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_2 ),
    inference(superposition,[],[f70,f87])).

fof(f87,plain,
    ( k1_tarski(sK0) = k2_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f70,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f544,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3)
        | r1_tarski(sK1,X3) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f540,f117])).

fof(f540,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3)
        | r1_tarski(sK1,X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3)
        | r1_tarski(sK1,X3)
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X3) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(superposition,[],[f67,f532])).

fof(f532,plain,
    ( ! [X0] :
        ( sK0 = sK8(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f531,f75])).

fof(f531,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,X0),k1_tarski(sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f530,f112])).

fof(f530,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,X0),k1_tarski(sK0))
        | r1_tarski(sK1,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f529,f117])).

fof(f529,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,X0),k1_tarski(sK0))
        | r1_tarski(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,X0),k1_tarski(sK0))
        | r1_tarski(sK1,X0)
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f406,f127])).

fof(f406,plain,
    ( ! [X10] :
        ( ~ r2_hidden(sK7(sK1,X10),k1_relat_1(sK1))
        | r2_hidden(sK8(sK1,X10),k1_tarski(sK0))
        | r1_tarski(sK1,X10) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f405,f112])).

fof(f405,plain,
    ( ! [X10] :
        ( r2_hidden(sK8(sK1,X10),k1_tarski(sK0))
        | ~ r2_hidden(sK7(sK1,X10),k1_relat_1(sK1))
        | r1_tarski(sK1,X10)
        | ~ v1_funct_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f386,f117])).

fof(f386,plain,
    ( ! [X10] :
        ( r2_hidden(sK8(sK1,X10),k1_tarski(sK0))
        | ~ r2_hidden(sK7(sK1,X10),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X10)
        | ~ v1_funct_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(superposition,[],[f140,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sK8(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | sK8(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f140,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f139,f117])).

fof(f139,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f135,f112])).

fof(f135,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3 ),
    inference(superposition,[],[f70,f92])).

fof(f92,plain,
    ( k1_tarski(sK0) = k2_relat_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f90])).

% (32473)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f562,plain,
    ( ~ spl9_17
    | spl9_1
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f557,f552,f80,f559])).

fof(f80,plain,
    ( spl9_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f552,plain,
    ( spl9_16
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f557,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl9_1
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f556,f82])).

fof(f82,plain,
    ( sK1 != sK2
    | spl9_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f556,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl9_16 ),
    inference(resolution,[],[f554,f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f554,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f552])).

fof(f555,plain,
    ( spl9_16
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f550,f115,f110,f105,f100,f95,f90,f85,f552])).

fof(f550,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f548,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK2,X0),k1_relat_1(sK1))
        | r1_tarski(sK2,X0) )
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f130,f102])).

fof(f130,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK2,X0),k1_relat_1(sK1))
        | r1_tarski(sK2,X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f129,f107])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK2,X0),k1_relat_1(sK1))
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl9_4 ),
    inference(superposition,[],[f127,f97])).

fof(f548,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK7(sK2,sK1),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f412,f368])).

fof(f368,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK0),sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f367,f117])).

fof(f367,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK0),sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f351,f112])).

fof(f351,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK0),sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK0),sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(superposition,[],[f76,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( sK0 = k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f140,f75])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f411,f107])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0)
        | r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0)
        | r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f67,f392])).

fof(f392,plain,
    ( ! [X2] :
        ( sK0 = sK8(sK2,X2)
        | r1_tarski(sK2,X2) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f391,f131])).

fof(f391,plain,
    ( ! [X2] :
        ( sK0 = sK8(sK2,X2)
        | r1_tarski(sK2,X2)
        | ~ r2_hidden(sK7(sK2,X2),k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f390,f102])).

fof(f390,plain,
    ( ! [X2] :
        ( sK0 = sK8(sK2,X2)
        | r1_tarski(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(sK7(sK2,X2),k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f378,f107])).

fof(f378,plain,
    ( ! [X2] :
        ( sK0 = sK8(sK2,X2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(sK7(sK2,X2),k1_relat_1(sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f128,f145])).

fof(f118,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f39,f115])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_relat_1(sK2)
    & k1_tarski(sK0) = k2_relat_1(sK1)
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X2) = k1_relat_1(X1)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_relat_1(X2) = k1_tarski(sK0)
          & k1_tarski(sK0) = k2_relat_1(sK1)
          & k1_relat_1(X2) = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_relat_1(X2) = k1_tarski(sK0)
        & k1_tarski(sK0) = k2_relat_1(sK1)
        & k1_relat_1(X2) = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_relat_1(sK2)
      & k1_tarski(sK0) = k2_relat_1(sK1)
      & k1_relat_1(sK1) = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X2) = k1_relat_1(X1) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X2) = k1_relat_1(X1) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

fof(f113,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f40,f110])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f41,f105])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    k1_tarski(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f45,f85])).

fof(f45,plain,(
    k1_tarski(sK0) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (32459)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.49  % (32466)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (32483)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (32482)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (32474)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (32474)Refutation not found, incomplete strategy% (32474)------------------------------
% 0.20/0.51  % (32474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32474)Memory used [KB]: 10618
% 0.20/0.51  % (32474)Time elapsed: 0.104 s
% 0.20/0.51  % (32474)------------------------------
% 0.20/0.51  % (32474)------------------------------
% 0.20/0.52  % (32462)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (32472)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (32480)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (32470)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (32463)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (32469)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (32468)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (32486)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (32464)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (32460)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (32461)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (32458)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (32462)Refutation not found, incomplete strategy% (32462)------------------------------
% 0.20/0.54  % (32462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32462)Memory used [KB]: 1918
% 0.20/0.54  % (32462)Time elapsed: 0.140 s
% 0.20/0.54  % (32462)------------------------------
% 0.20/0.54  % (32462)------------------------------
% 0.20/0.54  % (32475)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (32478)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (32479)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (32471)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (32485)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (32484)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (32487)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (32487)Refutation not found, incomplete strategy% (32487)------------------------------
% 0.20/0.56  % (32487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (32487)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (32487)Memory used [KB]: 1663
% 0.20/0.56  % (32487)Time elapsed: 0.148 s
% 0.20/0.56  % (32487)------------------------------
% 0.20/0.56  % (32487)------------------------------
% 0.20/0.56  % (32476)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (32477)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.57  % (32479)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (32467)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f602,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f555,f562,f594,f601])).
% 0.20/0.57  fof(f601,plain,(
% 0.20/0.57    ~spl9_7 | ~spl9_8 | spl9_17 | spl9_18),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f600])).
% 0.20/0.57  fof(f600,plain,(
% 0.20/0.57    $false | (~spl9_7 | ~spl9_8 | spl9_17 | spl9_18)),
% 0.20/0.57    inference(subsumption_resolution,[],[f599,f112])).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    v1_funct_1(sK1) | ~spl9_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    spl9_7 <=> v1_funct_1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.57  fof(f599,plain,(
% 0.20/0.57    ~v1_funct_1(sK1) | (~spl9_8 | spl9_17 | spl9_18)),
% 0.20/0.57    inference(subsumption_resolution,[],[f598,f561])).
% 0.20/0.57  fof(f561,plain,(
% 0.20/0.57    ~r1_tarski(sK1,sK2) | spl9_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f559])).
% 0.20/0.57  fof(f559,plain,(
% 0.20/0.57    spl9_17 <=> r1_tarski(sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.20/0.57  fof(f598,plain,(
% 0.20/0.57    r1_tarski(sK1,sK2) | ~v1_funct_1(sK1) | (~spl9_8 | spl9_18)),
% 0.20/0.57    inference(subsumption_resolution,[],[f596,f117])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    v1_relat_1(sK1) | ~spl9_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f115])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    spl9_8 <=> v1_relat_1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.57  fof(f596,plain,(
% 0.20/0.57    ~v1_relat_1(sK1) | r1_tarski(sK1,sK2) | ~v1_funct_1(sK1) | spl9_18),
% 0.20/0.57    inference(resolution,[],[f593,f127])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r2_hidden(sK7(X2,X3),k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X2,X3) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f125])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_relat_1(X2) | r2_hidden(sK7(X2,X3),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.57    inference(resolution,[],[f66,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.57    inference(nnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.57    inference(flattening,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(rectify,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.57  fof(f593,plain,(
% 0.20/0.57    ~r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1)) | spl9_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f591])).
% 0.20/0.57  fof(f591,plain,(
% 0.20/0.57    spl9_18 <=> r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.20/0.57  fof(f594,plain,(
% 0.20/0.57    ~spl9_18 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | spl9_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f589,f559,f115,f110,f105,f100,f95,f90,f85,f591])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    spl9_2 <=> k1_tarski(sK0) = k2_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    spl9_3 <=> k1_tarski(sK0) = k2_relat_1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl9_4 <=> k1_relat_1(sK1) = k1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    spl9_5 <=> v1_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    spl9_6 <=> v1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.57  fof(f589,plain,(
% 0.20/0.57    ~r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | spl9_17)),
% 0.20/0.57    inference(subsumption_resolution,[],[f588,f561])).
% 0.20/0.57  fof(f588,plain,(
% 0.20/0.57    r1_tarski(sK1,sK2) | ~r2_hidden(sK7(sK1,sK2),k1_relat_1(sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(resolution,[],[f544,f182])).
% 0.20/0.57  fof(f182,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f181])).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(forward_demodulation,[],[f180,f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    k1_relat_1(sK1) = k1_relat_1(sK2) | ~spl9_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f95])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(subsumption_resolution,[],[f179,f107])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    v1_relat_1(sK2) | ~spl9_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f105])).
% 0.20/0.57  fof(f179,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(subsumption_resolution,[],[f173,f102])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    v1_funct_1(sK2) | ~spl9_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f100])).
% 0.20/0.57  fof(f173,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(superposition,[],[f76,f145])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    ( ! [X0] : (sK0 = k1_funct_1(sK2,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(resolution,[],[f138,f75])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.57    inference(equality_resolution,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(rectify,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(forward_demodulation,[],[f137,f97])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl9_2 | ~spl9_5 | ~spl9_6)),
% 0.20/0.57    inference(subsumption_resolution,[],[f136,f107])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl9_2 | ~spl9_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f134,f102])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl9_2),
% 0.20/0.57    inference(superposition,[],[f70,f87])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    k1_tarski(sK0) = k2_relat_1(sK2) | ~spl9_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f85])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(rectify,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.57    inference(equality_resolution,[],[f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f544,plain,(
% 0.20/0.57    ( ! [X3] : (~r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3) | r1_tarski(sK1,X3)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f540,f117])).
% 0.20/0.57  fof(f540,plain,(
% 0.20/0.57    ( ! [X3] : (~r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3) | r1_tarski(sK1,X3) | ~v1_relat_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f537])).
% 0.20/0.57  fof(f537,plain,(
% 0.20/0.57    ( ! [X3] : (~r2_hidden(k4_tarski(sK7(sK1,X3),sK0),X3) | r1_tarski(sK1,X3) | ~v1_relat_1(sK1) | r1_tarski(sK1,X3)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(superposition,[],[f67,f532])).
% 0.20/0.57  fof(f532,plain,(
% 0.20/0.57    ( ! [X0] : (sK0 = sK8(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(resolution,[],[f531,f75])).
% 0.20/0.57  fof(f531,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK8(sK1,X0),k1_tarski(sK0)) | r1_tarski(sK1,X0)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f530,f112])).
% 0.20/0.57  fof(f530,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK8(sK1,X0),k1_tarski(sK0)) | r1_tarski(sK1,X0) | ~v1_funct_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f529,f117])).
% 0.20/0.57  fof(f529,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK8(sK1,X0),k1_tarski(sK0)) | r1_tarski(sK1,X0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f528])).
% 0.20/0.57  fof(f528,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK8(sK1,X0),k1_tarski(sK0)) | r1_tarski(sK1,X0) | ~v1_relat_1(sK1) | r1_tarski(sK1,X0) | ~v1_funct_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(resolution,[],[f406,f127])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    ( ! [X10] : (~r2_hidden(sK7(sK1,X10),k1_relat_1(sK1)) | r2_hidden(sK8(sK1,X10),k1_tarski(sK0)) | r1_tarski(sK1,X10)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f405,f112])).
% 0.20/0.57  fof(f405,plain,(
% 0.20/0.57    ( ! [X10] : (r2_hidden(sK8(sK1,X10),k1_tarski(sK0)) | ~r2_hidden(sK7(sK1,X10),k1_relat_1(sK1)) | r1_tarski(sK1,X10) | ~v1_funct_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f386,f117])).
% 0.20/0.57  fof(f386,plain,(
% 0.20/0.57    ( ! [X10] : (r2_hidden(sK8(sK1,X10),k1_tarski(sK0)) | ~r2_hidden(sK7(sK1,X10),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r1_tarski(sK1,X10) | ~v1_funct_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.57    inference(superposition,[],[f140,f128])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK8(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(X0,X1) | ~v1_funct_1(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f124])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_relat_1(X0) | sK8(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f66,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  fof(f140,plain,(
% 0.20/0.58    ( ! [X1] : (r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(subsumption_resolution,[],[f139,f117])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    ( ! [X1] : (r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl9_3 | ~spl9_7)),
% 0.20/0.58    inference(subsumption_resolution,[],[f135,f112])).
% 0.20/0.58  fof(f135,plain,(
% 0.20/0.58    ( ! [X1] : (r2_hidden(k1_funct_1(sK1,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl9_3),
% 0.20/0.58    inference(superposition,[],[f70,f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    k1_tarski(sK0) = k2_relat_1(sK1) | ~spl9_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f90])).
% 0.20/0.58  % (32473)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f38])).
% 0.20/0.58  fof(f562,plain,(
% 0.20/0.58    ~spl9_17 | spl9_1 | ~spl9_16),
% 0.20/0.58    inference(avatar_split_clause,[],[f557,f552,f80,f559])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    spl9_1 <=> sK1 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.58  fof(f552,plain,(
% 0.20/0.58    spl9_16 <=> r1_tarski(sK2,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.58  fof(f557,plain,(
% 0.20/0.58    ~r1_tarski(sK1,sK2) | (spl9_1 | ~spl9_16)),
% 0.20/0.58    inference(subsumption_resolution,[],[f556,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    sK1 != sK2 | spl9_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f80])).
% 0.20/0.58  fof(f556,plain,(
% 0.20/0.58    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl9_16),
% 0.20/0.58    inference(resolution,[],[f554,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f554,plain,(
% 0.20/0.58    r1_tarski(sK2,sK1) | ~spl9_16),
% 0.20/0.58    inference(avatar_component_clause,[],[f552])).
% 0.20/0.58  fof(f555,plain,(
% 0.20/0.58    spl9_16 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8),
% 0.20/0.58    inference(avatar_split_clause,[],[f550,f115,f110,f105,f100,f95,f90,f85,f552])).
% 0.20/0.58  fof(f550,plain,(
% 0.20/0.58    r1_tarski(sK2,sK1) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(subsumption_resolution,[],[f548,f131])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK7(sK2,X0),k1_relat_1(sK1)) | r1_tarski(sK2,X0)) ) | (~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f130,f102])).
% 0.20/0.58  fof(f130,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK7(sK2,X0),k1_relat_1(sK1)) | r1_tarski(sK2,X0) | ~v1_funct_1(sK2)) ) | (~spl9_4 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f129,f107])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK7(sK2,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK2) | r1_tarski(sK2,X0) | ~v1_funct_1(sK2)) ) | ~spl9_4),
% 0.20/0.58    inference(superposition,[],[f127,f97])).
% 0.20/0.58  fof(f548,plain,(
% 0.20/0.58    r1_tarski(sK2,sK1) | ~r2_hidden(sK7(sK2,sK1),k1_relat_1(sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(resolution,[],[f412,f368])).
% 0.20/0.58  fof(f368,plain,(
% 0.20/0.58    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK0),sK1) | ~r2_hidden(X3,k1_relat_1(sK1))) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(subsumption_resolution,[],[f367,f117])).
% 0.20/0.58  fof(f367,plain,(
% 0.20/0.58    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK0),sK1) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(subsumption_resolution,[],[f351,f112])).
% 0.20/0.58  fof(f351,plain,(
% 0.20/0.58    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK0),sK1) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f346])).
% 0.20/0.58  fof(f346,plain,(
% 0.20/0.58    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK0),sK1) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X3,k1_relat_1(sK1))) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(superposition,[],[f76,f195])).
% 0.20/0.58  fof(f195,plain,(
% 0.20/0.58    ( ! [X0] : (sK0 = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl9_3 | ~spl9_7 | ~spl9_8)),
% 0.20/0.58    inference(resolution,[],[f140,f75])).
% 0.20/0.58  fof(f412,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0) | r1_tarski(sK2,X0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f411,f107])).
% 0.20/0.58  fof(f411,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0) | r1_tarski(sK2,X0) | ~v1_relat_1(sK2)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f408])).
% 0.20/0.58  fof(f408,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK2,X0),sK0),X0) | r1_tarski(sK2,X0) | ~v1_relat_1(sK2) | r1_tarski(sK2,X0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(superposition,[],[f67,f392])).
% 0.20/0.58  fof(f392,plain,(
% 0.20/0.58    ( ! [X2] : (sK0 = sK8(sK2,X2) | r1_tarski(sK2,X2)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f391,f131])).
% 0.20/0.58  fof(f391,plain,(
% 0.20/0.58    ( ! [X2] : (sK0 = sK8(sK2,X2) | r1_tarski(sK2,X2) | ~r2_hidden(sK7(sK2,X2),k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f390,f102])).
% 0.20/0.58  fof(f390,plain,(
% 0.20/0.58    ( ! [X2] : (sK0 = sK8(sK2,X2) | r1_tarski(sK2,X2) | ~v1_funct_1(sK2) | ~r2_hidden(sK7(sK2,X2),k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f378,f107])).
% 0.20/0.58  fof(f378,plain,(
% 0.20/0.58    ( ! [X2] : (sK0 = sK8(sK2,X2) | ~v1_relat_1(sK2) | r1_tarski(sK2,X2) | ~v1_funct_1(sK2) | ~r2_hidden(sK7(sK2,X2),k1_relat_1(sK1))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.20/0.58    inference(superposition,[],[f128,f145])).
% 0.20/0.58  fof(f118,plain,(
% 0.20/0.58    spl9_8),
% 0.20/0.58    inference(avatar_split_clause,[],[f39,f115])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    v1_relat_1(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.58    inference(flattening,[],[f11])).
% 0.20/0.58  fof(f11,plain,(
% 0.20/0.58    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.20/0.58    inference(negated_conjecture,[],[f9])).
% 0.20/0.58  fof(f9,conjecture,(
% 0.20/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    spl9_7),
% 0.20/0.58    inference(avatar_split_clause,[],[f40,f110])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    v1_funct_1(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    spl9_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f41,f105])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    v1_relat_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    spl9_5),
% 0.20/0.58    inference(avatar_split_clause,[],[f42,f100])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    v1_funct_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    spl9_4),
% 0.20/0.58    inference(avatar_split_clause,[],[f43,f95])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    spl9_3),
% 0.20/0.58    inference(avatar_split_clause,[],[f44,f90])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    k1_tarski(sK0) = k2_relat_1(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    spl9_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f45,f85])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    k1_tarski(sK0) = k2_relat_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ~spl9_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f46,f80])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    sK1 != sK2),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (32479)------------------------------
% 0.20/0.58  % (32479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (32479)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (32479)Memory used [KB]: 6524
% 0.20/0.58  % (32479)Time elapsed: 0.172 s
% 0.20/0.58  % (32479)------------------------------
% 0.20/0.58  % (32479)------------------------------
% 0.20/0.58  % (32457)Success in time 0.222 s
%------------------------------------------------------------------------------
