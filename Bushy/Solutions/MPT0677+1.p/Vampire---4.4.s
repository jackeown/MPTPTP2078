%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t121_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 93.79s
% Output     : Refutation 93.79s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 441 expanded)
%              Number of leaves         :   21 ( 135 expanded)
%              Depth                    :   18
%              Number of atoms          :  538 (2640 expanded)
%              Number of equality atoms :  103 ( 592 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f274,f297,f593,f1462,f1815,f8690,f8755])).

fof(f8755,plain,
    ( ~ spl12_35
    | spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f8089,f272,f263,f3408])).

fof(f3408,plain,
    ( spl12_35
  <=> ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f263,plain,
    ( spl12_1
  <=> ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f272,plain,
    ( spl12_2
  <=> r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f8089,plain,
    ( ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f264,f3111])).

fof(f3111,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),X2)
        | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,X2)) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f3110,f75])).

fof(f75,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k3_xboole_0(sK0,sK1))
    & v2_funct_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k3_xboole_0(X0,X1))
        & v2_funct_1(X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k3_xboole_0(sK0,sK1))
      & v2_funct_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k3_xboole_0(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k3_xboole_0(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',t121_funct_1)).

fof(f3110,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,X2))
        | ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),X2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f3109,f76])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f3109,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,X2))
        | ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f3080,f1841])).

fof(f1841,plain,
    ( r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k1_relat_1(sK2))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f75,f76,f273,f124])).

fof(f124,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK6(X0,X1,X2)) = sK5(X0,X1,X2)
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).

fof(f57,plain,(
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
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',d12_funct_1)).

fof(f273,plain,
    ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f272])).

fof(f3080,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,X2))
        | ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),X2)
        | ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_2 ),
    inference(superposition,[],[f121,f1843])).

fof(f1843,plain,
    ( k1_funct_1(sK2,sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))))) = sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f75,f76,f273,f122])).

fof(f122,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f121,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f264,plain,
    ( ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f263])).

fof(f8690,plain,
    ( ~ spl12_2
    | ~ spl12_4
    | spl12_35 ),
    inference(avatar_contradiction_clause,[],[f8689])).

fof(f8689,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f8647,f5944])).

fof(f5944,plain,
    ( ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK1)
    | ~ spl12_2
    | ~ spl12_35 ),
    inference(unit_resulting_resolution,[],[f1842,f3409,f127])).

fof(f127,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK10(X0,X1,X2),X1)
            | ~ r2_hidden(sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK10(X0,X1,X2),X1)
              & r2_hidden(sK10(X0,X1,X2),X0) )
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK10(X0,X1,X2),X1)
          | ~ r2_hidden(sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(sK10(X0,X1,X2),X0) )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',d4_xboole_0)).

fof(f3409,plain,
    ( ~ r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl12_35 ),
    inference(avatar_component_clause,[],[f3408])).

fof(f1842,plain,
    ( r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK0)
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f75,f76,f273,f123])).

fof(f123,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f8647,plain,
    ( r2_hidden(sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK1)
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(backward_demodulation,[],[f8624,f1534])).

fof(f1534,plain,
    ( r2_hidden(sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),sK1)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f75,f76,f296,f123])).

fof(f296,plain,
    ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl12_4
  <=> r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f8624,plain,
    ( sK7(sK2,sK0,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f1841,f1843,f3060])).

fof(f3060,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) != sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
        | sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK2)) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3059,f75])).

fof(f3059,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) != sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
        | sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3058,f76])).

fof(f3058,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) != sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
        | sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3057,f77])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f3057,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) != sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
        | sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3024,f1533])).

fof(f1533,plain,
    ( r2_hidden(sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k1_relat_1(sK2))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f75,f76,f296,f124])).

fof(f3024,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) != sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
        | sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))) = X5
        | ~ r2_hidden(sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),k1_relat_1(sK2))
        | ~ r2_hidden(X5,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_4 ),
    inference(superposition,[],[f82,f1535])).

fof(f1535,plain,
    ( k1_funct_1(sK2,sK7(sK2,sK1,sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))))) = sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f75,f76,f296,f122])).

fof(f82,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',d8_funct_1)).

fof(f1815,plain,
    ( ~ spl12_0
    | spl12_3 ),
    inference(avatar_contradiction_clause,[],[f1791])).

fof(f1791,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f132,f267,f1488,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f66,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',d3_tarski)).

fof(f1488,plain,
    ( ! [X0] : ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),X0))
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f270,f129])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f270,plain,
    ( ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl12_3
  <=> ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f267,plain,
    ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl12_0
  <=> r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f132,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f75,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',t154_relat_1)).

fof(f1462,plain,
    ( ~ spl12_0
    | spl12_5 ),
    inference(avatar_contradiction_clause,[],[f1439])).

fof(f1439,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_5 ),
    inference(unit_resulting_resolution,[],[f168,f267,f619,f104])).

fof(f619,plain,
    ( ! [X0] : ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k9_relat_1(sK2,sK1),X0))
    | ~ spl12_5 ),
    inference(unit_resulting_resolution,[],[f293,f129])).

fof(f293,plain,
    ( ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl12_5
  <=> ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f168,plain,(
    ! [X12,X11] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X12,X11)),k3_xboole_0(k9_relat_1(sK2,X11),k9_relat_1(sK2,X12))) ),
    inference(superposition,[],[f132,f97])).

fof(f97,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t121_funct_1.p',commutativity_k3_xboole_0)).

fof(f593,plain,
    ( ~ spl12_5
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f556,f272,f266,f292])).

fof(f556,plain,
    ( ~ r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f78,f273,f267,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK10(X0,X1,X2),X1)
      | ~ r2_hidden(sK10(X0,X1,X2),X0)
      | ~ r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f78,plain,(
    k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f297,plain,
    ( spl12_0
    | spl12_4 ),
    inference(avatar_split_clause,[],[f282,f295,f266])).

fof(f282,plain,
    ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X1] :
      ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) != X1
      | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X1),k9_relat_1(sK2,sK1))
      | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X1),X1) ) ),
    inference(superposition,[],[f78,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK10(X0,X1,X2),X1)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f274,plain,
    ( spl12_0
    | spl12_2 ),
    inference(avatar_split_clause,[],[f253,f272,f266])).

fof(f253,plain,
    ( r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) != X0
      | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X0),k9_relat_1(sK2,sK0))
      | r2_hidden(sK10(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1),X0),X0) ) ),
    inference(superposition,[],[f78,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK10(X0,X1,X2),X0)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
