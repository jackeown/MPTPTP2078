%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t154_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:17 EDT 2019

% Result     : Theorem 94.32s
% Output     : Refutation 94.32s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 838 expanded)
%              Number of leaves         :   19 ( 234 expanded)
%              Depth                    :   17
%              Number of atoms          :  752 (4759 expanded)
%              Number of equality atoms :  198 (1277 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f236,f256,f22862,f22871,f22966,f23190])).

fof(f23190,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f23189])).

fof(f23189,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f23188,f226])).

fof(f226,plain,
    ( ~ r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl13_1
  <=> ~ r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f23188,plain,
    ( r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(forward_demodulation,[],[f23178,f22899])).

fof(f22899,plain,
    ( k1_funct_1(sK1,sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))) = sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f79,f80,f235,f143])).

fof(f143,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f58,f61,f60,f59])).

fof(f59,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',d5_funct_1)).

fof(f235,plain,
    ( r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl13_2
  <=> r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f80,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',t154_funct_1)).

fof(f79,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f23178,plain,
    ( r2_hidden(k1_funct_1(sK1,sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))),k9_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f79,f80,f22898,f23144,f149])).

fof(f149,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK8(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK9(X0,X1,X2)) = sK8(X0,X1,X2)
                  & r2_hidden(sK9(X0,X1,X2),X1)
                  & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
                    & r2_hidden(sK10(X0,X1,X6),X1)
                    & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f69,f72,f71,f70])).

fof(f70,plain,(
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
              ( k1_funct_1(X0,X4) != sK8(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK8(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X2)) = X3
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
        & r2_hidden(sK10(X0,X1,X6),X1)
        & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
    inference(rectify,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',d12_funct_1)).

fof(f23144,plain,
    ( r2_hidden(sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0)
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f23143,f255])).

fof(f255,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl13_4
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f23143,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))) = sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f23121,f22899])).

fof(f23121,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))))) = sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f155,f156,f22898,f133])).

fof(f133,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK2(X0,X1)) != sK3(X0,X1)
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( k1_funct_1(X0,sK3(X0,X1)) != sK2(X0,X1)
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & k1_funct_1(X1,sK2(X0,X1)) = sK3(X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f55])).

fof(f55,plain,(
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
     => ( ( ( k1_funct_1(X1,sK2(X0,X1)) != sK3(X0,X1)
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( k1_funct_1(X0,sK3(X0,X1)) != sK2(X0,X1)
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & k1_funct_1(X1,sK2(X0,X1)) = sK3(X0,X1)
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',t54_funct_1)).

fof(f156,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f80,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',dt_k2_funct_1)).

fof(f155,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f80,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f22898,plain,
    ( r2_hidden(sK6(sK1,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f79,f80,f235,f144])).

fof(f144,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f22966,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f22965])).

fof(f22965,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f22964,f235])).

fof(f22964,plain,
    ( ~ r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl13_0
    | ~ spl13_4 ),
    inference(forward_demodulation,[],[f22948,f195])).

fof(f195,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f155,f156,f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f22948,plain,
    ( ~ r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k1_relat_1(k2_funct_1(sK1)))
    | ~ spl13_0
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f155,f156,f82,f229,f255,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
                | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
                  & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t154_funct_1.p',d13_funct_1)).

fof(f229,plain,
    ( r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl13_0
  <=> r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f82,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f22871,plain,
    ( spl13_4
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f22865,f228,f254])).

fof(f22865,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0)
    | ~ spl13_0 ),
    inference(backward_demodulation,[],[f22863,f16647])).

fof(f16647,plain,
    ( r2_hidden(sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0)
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f79,f80,f229,f151])).

fof(f151,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f22863,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))) = sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))
    | ~ spl13_0 ),
    inference(forward_demodulation,[],[f22837,f16648])).

fof(f16648,plain,
    ( k1_funct_1(sK1,sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))) = sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f79,f80,f229,f150])).

fof(f150,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f22837,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))))) = sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f155,f156,f16646,f133])).

fof(f16646,plain,
    ( r2_hidden(sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f79,f80,f229,f152])).

fof(f152,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f22862,plain,
    ( spl13_2
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f22861,f228,f234])).

fof(f22861,plain,
    ( r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl13_0 ),
    inference(forward_demodulation,[],[f22838,f16648])).

fof(f22838,plain,
    ( r2_hidden(k1_funct_1(sK1,sK10(sK1,sK0,sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)))),k2_relat_1(sK1))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f155,f156,f16646,f135])).

fof(f135,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f256,plain,
    ( spl13_0
    | spl13_4 ),
    inference(avatar_split_clause,[],[f241,f254,f228])).

fof(f241,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0))),sK0)
    | r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f183])).

fof(f183,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,sK0) != X1
      | r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,X1)),sK0)
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f182,f155])).

fof(f182,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,sK0) != X1
      | r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,X1)),sK0)
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X1),X1)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f163,f156])).

fof(f163,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,sK0) != X1
      | r2_hidden(k1_funct_1(k2_funct_1(sK1),sK7(k2_funct_1(sK1),sK0,X1)),sK0)
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X1),X1)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f82,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f236,plain,
    ( spl13_0
    | spl13_2 ),
    inference(avatar_split_clause,[],[f215,f234,f228])).

fof(f215,plain,
    ( r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | r2_hidden(sK7(k2_funct_1(sK1),sK0,k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,sK0) != X0
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),k2_relat_1(sK1))
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),X0) ) ),
    inference(backward_demodulation,[],[f195,f181])).

fof(f181,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,sK0) != X0
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f180,f155])).

fof(f180,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,sK0) != X0
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),X0)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f162,f156])).

fof(f162,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,sK0) != X0
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK7(k2_funct_1(sK1),sK0,X0),X0)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f82,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
