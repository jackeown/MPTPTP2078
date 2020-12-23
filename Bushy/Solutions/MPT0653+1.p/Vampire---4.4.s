%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t60_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 941 expanded)
%              Number of leaves         :   13 ( 273 expanded)
%              Depth                    :   35
%              Number of atoms          :  726 (11296 expanded)
%              Number of equality atoms :  231 (5135 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f243,f501,f633])).

fof(f633,plain,
    ( ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f631,f521])).

fof(f521,plain,
    ( r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f512,f503])).

fof(f503,plain,
    ( r2_hidden(k1_funct_1(sK1,sK8(sK1,sK2)),k1_relat_1(sK2))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f242,f123])).

fof(f123,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_funct_1(sK1) != sK2
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK1,X2) = X3
            | k1_funct_1(sK2,X3) != X2 )
          & ( k1_funct_1(sK2,X3) = X2
            | k1_funct_1(sK1,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    & k1_relat_1(sK2) = k2_relat_1(sK1)
    & k1_relat_1(sK1) = k2_relat_1(sK2)
    & v2_funct_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X1) = k2_relat_1(X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK1) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK1,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK1,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK1)) )
          & k1_relat_1(X1) = k2_relat_1(sK1)
          & k1_relat_1(sK1) = k2_relat_1(X1)
          & v2_funct_1(sK1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK2
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK2,X3) != X2 )
              & ( k1_funct_1(sK2,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK2))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k1_relat_1(sK2) = k2_relat_1(X0)
        & k1_relat_1(X0) = k2_relat_1(sK2)
        & v2_funct_1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k1_relat_1(X1) = k2_relat_1(X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',t60_funct_1)).

fof(f122,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f119,f54])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f89,f59])).

fof(f59,plain,(
    k1_relat_1(sK2) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f41,plain,(
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

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',d5_funct_1)).

fof(f242,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl9_6
  <=> r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f512,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f220,f233])).

fof(f233,plain,
    ( sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl9_4
  <=> sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f220,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2) ),
    inference(subsumption_resolution,[],[f219,f55])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f219,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f218,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f218,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f217,f62])).

fof(f62,plain,(
    k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f217,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | k2_funct_1(sK1) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | k1_funct_1(sK1,sK8(sK1,X1)) = sK7(sK1,X1)
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f193,f53])).

fof(f193,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | k1_funct_1(sK1,sK8(sK1,X1)) = sK7(sK1,X1)
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f192,f54])).

fof(f192,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | k1_funct_1(sK1,sK8(sK1,X1)) = sK7(sK1,X1)
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f57,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f187,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | k1_funct_1(sK1,sK8(sK1,X1)) = sK7(sK1,X1)
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f84,f59])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | k1_funct_1(X0,sK8(X0,X1)) = sK7(X0,X1)
      | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK7(X0,X1)) != sK8(X0,X1)
                  | ~ r2_hidden(sK7(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK8(X0,X1)) = sK7(X0,X1)
                & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ~ sP0(X2,X3,X0,X1) )
     => ( ( ( k1_funct_1(X1,sK7(X0,X1)) != sK8(X0,X1)
            | ~ r2_hidden(sK7(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK8(X0,X1)) = sK7(X0,X1)
          & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) )
        | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
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
                  & sP0(X2,X3,X0,X1) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',t54_funct_1)).

fof(f631,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f630,f59])).

fof(f630,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f629,f53])).

fof(f629,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f628,f54])).

fof(f628,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f627,f57])).

fof(f627,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f626,f55])).

fof(f626,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f625,f56])).

fof(f625,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f624,f59])).

fof(f624,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f623,f233])).

fof(f623,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f619,f62])).

fof(f619,plain,
    ( k2_funct_1(sK1) = sK2
    | ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(trivial_inequality_removal,[],[f611])).

fof(f611,plain,
    ( sK8(sK1,sK2) != sK8(sK1,sK2)
    | k2_funct_1(sK1) = sK2
    | ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f85,f608])).

fof(f608,plain,
    ( k1_funct_1(sK2,sK7(sK1,sK2)) = sK8(sK1,sK2)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f531,f521])).

fof(f531,plain,
    ( k1_funct_1(sK2,sK7(sK1,sK2)) = sK8(sK1,sK2)
    | ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f530,f512])).

fof(f530,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,sK2))) = sK8(sK1,sK2)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f523,f242])).

fof(f523,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,sK2))) = sK8(sK1,sK2)
    | ~ r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_4 ),
    inference(superposition,[],[f87,f512])).

fof(f87,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(sK2))
      | k1_funct_1(sK2,k1_funct_1(sK1,X2)) = X2
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK2,X3) = X2
      | k1_funct_1(sK1,X2) != X3
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK7(X0,X1)) != sK8(X0,X1)
      | k2_funct_1(X0) = X1
      | ~ r2_hidden(sK7(X0,X1),k2_relat_1(X0))
      | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f501,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f499,f246])).

fof(f246,plain,
    ( r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f245,f59])).

fof(f245,plain,
    ( r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f236,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(X0,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( k1_funct_1(X2,X1) != X0
            | ~ r2_hidden(X1,k1_relat_1(X2)) )
          & k1_funct_1(X3,X0) = X1
          & r2_hidden(X0,k2_relat_1(X2)) ) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | k1_funct_1(X3,X0) != X1
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f236,plain,
    ( ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl9_5
  <=> ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f499,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f495,f59])).

fof(f495,plain,
    ( ~ r2_hidden(sK7(sK1,sK2),k2_relat_1(sK1))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f53,f54,f57,f55,f56,f62,f59,f244,f493,f85])).

fof(f493,plain,
    ( ! [X3] : sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,X3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f477,f300])).

fof(f300,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f244,f258])).

fof(f258,plain,
    ( r2_hidden(k1_funct_1(sK2,sK7(sK1,sK2)),k1_relat_1(sK1))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f246,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f120,f55])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f89,f58])).

fof(f58,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f477,plain,
    ( ! [X3] :
        ( sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,X3)
        | ~ r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f92,f466])).

fof(f466,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f312,f300])).

fof(f312,plain,
    ( k1_funct_1(sK1,sK8(sK1,sK2)) = sK7(sK1,sK2)
    | ~ r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f311,f244])).

fof(f311,plain,
    ( ~ r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | k1_funct_1(sK1,k1_funct_1(sK2,sK7(sK1,sK2))) = sK7(sK1,sK2)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f303,f246])).

fof(f303,plain,
    ( ~ r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ r2_hidden(sK7(sK1,sK2),k1_relat_1(sK2))
    | k1_funct_1(sK1,k1_funct_1(sK2,sK7(sK1,sK2))) = sK7(sK1,sK2)
    | ~ spl9_5 ),
    inference(superposition,[],[f86,f244])).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | k1_funct_1(sK1,k1_funct_1(sK2,X3)) = X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) = X3
      | k1_funct_1(sK2,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X2,X1),X1,X2,X3)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f244,plain,
    ( k1_funct_1(sK2,sK7(sK1,sK2)) = sK8(sK1,sK2)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f236,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X3,X0) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f243,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f205,f241,f235])).

fof(f205,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2) ),
    inference(subsumption_resolution,[],[f204,f55])).

fof(f204,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f56])).

fof(f203,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f62])).

fof(f202,plain,
    ( r2_hidden(sK8(sK1,sK2),k1_relat_1(sK1))
    | ~ sP0(sK7(sK1,sK2),sK8(sK1,sK2),sK1,sK2)
    | k2_funct_1(sK1) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f178,f53])).

fof(f178,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f177,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f172,f57])).

fof(f172,plain,(
    ! [X1] :
      ( k1_relat_1(sK2) != k1_relat_1(X1)
      | r2_hidden(sK8(sK1,X1),k1_relat_1(sK1))
      | ~ sP0(sK7(sK1,X1),sK8(sK1,X1),sK1,X1)
      | k2_funct_1(sK1) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f83,f59])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | r2_hidden(sK8(X0,X1),k1_relat_1(X0))
      | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
