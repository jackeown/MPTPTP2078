%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t126_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 223.32s
% Output     : Refutation 223.32s
% Verified   : 
% Statistics : Number of formulae       :  108 (1091 expanded)
%              Number of leaves         :   19 ( 318 expanded)
%              Depth                    :   17
%              Number of atoms          :  548 (5413 expanded)
%              Number of equality atoms :   92 (1265 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f236,f2178,f8197])).

fof(f8197,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f8196])).

fof(f8196,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f8194,f203])).

fof(f203,plain,
    ( ~ r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl12_1
  <=> ~ r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f8194,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(backward_demodulation,[],[f8191,f8162])).

fof(f8162,plain,
    ( r2_hidden(k1_funct_1(k8_relat_1(sK2,sK4),sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f119,f123,f2256,f4886,f114])).

fof(f114,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK8(X0,X1,X2)) = sK7(X0,X1,X2)
                  & r2_hidden(sK8(X0,X1,X2),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                    & r2_hidden(sK9(X0,X1,X6),X1)
                    & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f57,f60,f59,f58])).

fof(f58,plain,(
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
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X1,X2)) = X3
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',d12_funct_1)).

fof(f4886,plain,
    ( r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(k8_relat_1(sK2,sK4)))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f214,f212,f2728])).

fof(f2728,plain,
    ( ! [X2,X3] :
        ( ~ sP0(sK4,X3,X2)
        | r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(X3))
        | ~ r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),X2) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f2706,f2255])).

fof(f2255,plain,
    ( r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(sK4))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f235,f117])).

fof(f117,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f235,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(sK4,sK3))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl12_4
  <=> r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k9_relat_1(k8_relat_1(sK2,sK4),sK3) != k3_xboole_0(sK2,k9_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK2,sK4),sK3) != k3_xboole_0(sK2,k9_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',t126_funct_1)).

fof(f69,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f2706,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),X2)
        | r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(X3))
        | ~ r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(sK4))
        | ~ sP0(sK4,X3,X2) )
    | ~ spl12_4 ),
    inference(superposition,[],[f95,f2257])).

fof(f2257,plain,
    ( k1_funct_1(sK4,sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f235,f115])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK10(X0,X1)) != k1_funct_1(X1,sK10(X0,X1))
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK11(X0,X1,X2)),X2)
            | ~ r2_hidden(sK11(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK11(X0,X1,X2)),X2)
              & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK10(X0,X1)) != k1_funct_1(X1,sK10(X0,X1))
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK11(X0,X1,X2)),X2)
          | ~ r2_hidden(sK11(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK11(X0,X1,X2)),X2)
            & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
                & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f212,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl12_2
  <=> r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f214,plain,(
    ! [X0] : sP0(sK4,k8_relat_1(X0,sK4),X0) ),
    inference(unit_resulting_resolution,[],[f141,f118])).

fof(f118,plain,(
    ! [X2,X0] :
      ( sP0(X2,k8_relat_1(X0,X2),X0)
      | ~ sP1(X0,k8_relat_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f141,plain,(
    ! [X0,X1] : sP1(X0,k8_relat_1(X1,sK4),sK4) ),
    inference(unit_resulting_resolution,[],[f69,f70,f119,f123,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f35,f44,f43])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',t85_funct_1)).

fof(f2256,plain,
    ( r2_hidden(sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),sK3)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f235,f116])).

fof(f116,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f123,plain,(
    ! [X0] : v1_funct_1(k8_relat_1(X0,sK4)) ),
    inference(unit_resulting_resolution,[],[f69,f70,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',fc9_funct_1)).

fof(f119,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK4)) ),
    inference(unit_resulting_resolution,[],[f69,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',dt_k8_relat_1)).

fof(f8191,plain,
    ( k1_funct_1(k8_relat_1(sK2,sK4),sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(forward_demodulation,[],[f8158,f2257])).

fof(f8158,plain,
    ( k1_funct_1(sK4,sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = k1_funct_1(k8_relat_1(sK2,sK4),sK9(sK4,sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f214,f4886,f96])).

fof(f96,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2178,plain,(
    ~ spl12_0 ),
    inference(avatar_contradiction_clause,[],[f2177])).

fof(f2177,plain,
    ( $false
    | ~ spl12_0 ),
    inference(subsumption_resolution,[],[f2157,f2138])).

fof(f2138,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(sK4,sK3))
    | ~ spl12_0 ),
    inference(forward_demodulation,[],[f2107,f876])).

fof(f876,plain,
    ( k1_funct_1(sK4,sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_0 ),
    inference(forward_demodulation,[],[f850,f301])).

fof(f301,plain,
    ( k1_funct_1(k8_relat_1(sK2,sK4),sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f119,f123,f206,f115])).

fof(f206,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl12_0
  <=> r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f850,plain,
    ( k1_funct_1(sK4,sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))) = k1_funct_1(k8_relat_1(sK2,sK4),sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f214,f299,f96])).

fof(f299,plain,
    ( r2_hidden(sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(k8_relat_1(sK2,sK4)))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f119,f123,f206,f117])).

fof(f2107,plain,
    ( r2_hidden(k1_funct_1(sK4,sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))),k9_relat_1(sK4,sK3))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f69,f70,f300,f848,f114])).

fof(f848,plain,
    ( r2_hidden(sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),k1_relat_1(sK4))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f214,f299,f93])).

fof(f93,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f300,plain,
    ( r2_hidden(sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3))),sK3)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f119,f123,f206,f116])).

fof(f2157,plain,
    ( ~ r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(sK4,sK3))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f71,f206,f877,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t126_funct_1.p',d4_xboole_0)).

fof(f877,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),sK2)
    | ~ spl12_0 ),
    inference(forward_demodulation,[],[f849,f876])).

fof(f849,plain,
    ( r2_hidden(k1_funct_1(sK4,sK9(k8_relat_1(sK2,sK4),sK3,sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)))),sK2)
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f214,f299,f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f71,plain,(
    k9_relat_1(k8_relat_1(sK2,sK4),sK3) != k3_xboole_0(sK2,k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f236,plain,
    ( spl12_0
    | spl12_4 ),
    inference(avatar_split_clause,[],[f221,f234,f205])).

fof(f221,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(sK4,sK3))
    | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3)) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X1] :
      ( k9_relat_1(k8_relat_1(sK2,sK4),sK3) != X1
      | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),X1),k9_relat_1(sK4,sK3))
      | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),X1),X1) ) ),
    inference(superposition,[],[f71,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f213,plain,
    ( spl12_0
    | spl12_2 ),
    inference(avatar_split_clause,[],[f192,f211,f205])).

fof(f192,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),sK2)
    | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),k9_relat_1(k8_relat_1(sK2,sK4),sK3)),k9_relat_1(k8_relat_1(sK2,sK4),sK3)) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( k9_relat_1(k8_relat_1(sK2,sK4),sK3) != X0
      | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),X0),sK2)
      | r2_hidden(sK5(sK2,k9_relat_1(sK4,sK3),X0),X0) ) ),
    inference(superposition,[],[f71,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
