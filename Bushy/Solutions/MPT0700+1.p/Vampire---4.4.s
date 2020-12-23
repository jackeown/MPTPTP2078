%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t155_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:17 EDT 2019

% Result     : Theorem 92.99s
% Output     : Refutation 92.99s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 916 expanded)
%              Number of leaves         :   19 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          :  741 (5151 expanded)
%              Number of equality atoms :  209 (1394 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1959,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f252,f1189,f1931])).

fof(f1931,plain,(
    ~ spl13_0 ),
    inference(avatar_contradiction_clause,[],[f1930])).

fof(f1930,plain,
    ( $false
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f1900,f1416])).

fof(f1416,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)))) = sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f144,f145,f1214,f124])).

fof(f124,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f49])).

fof(f49,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',t54_funct_1)).

fof(f1214,plain,
    ( r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f73,f74,f228,f138])).

fof(f138,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f60])).

fof(f60,plain,(
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

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',d13_funct_1)).

fof(f228,plain,
    ( r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl13_0
  <=> r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f145,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f73,f74,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',dt_k2_funct_1)).

fof(f144,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f73,f74,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',t155_funct_1)).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f1900,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)))) != sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f76,f228,f1215,f1418,f348])).

fof(f348,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | k9_relat_1(k2_funct_1(sK1),X18) = X19
      | k1_funct_1(k2_funct_1(sK1),X17) != sK8(k2_funct_1(sK1),X18,X19)
      | ~ r2_hidden(X17,k2_relat_1(sK1))
      | ~ r2_hidden(sK8(k2_funct_1(sK1),X18,X19),X19) ) ),
    inference(subsumption_resolution,[],[f347,f144])).

fof(f347,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X17,k2_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),X18) = X19
      | k1_funct_1(k2_funct_1(sK1),X17) != sK8(k2_funct_1(sK1),X18,X19)
      | ~ r2_hidden(X17,X18)
      | ~ r2_hidden(sK8(k2_funct_1(sK1),X18,X19),X19)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f293,f145])).

fof(f293,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X17,k2_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),X18) = X19
      | k1_funct_1(k2_funct_1(sK1),X17) != sK8(k2_funct_1(sK1),X18,X19)
      | ~ r2_hidden(X17,X18)
      | ~ r2_hidden(sK8(k2_funct_1(sK1),X18,X19),X19)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f114,f183])).

fof(f183,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f144,f145,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK8(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f63,f66,f65,f64])).

fof(f64,plain,(
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

fof(f65,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X2)) = X3
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
        & r2_hidden(sK10(X0,X1,X6),X1)
        & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',d12_funct_1)).

fof(f1418,plain,
    ( r2_hidden(k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f73,f74,f1214,f133])).

fof(f133,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f52,f55,f54,f53])).

fof(f53,plain,(
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

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t155_funct_1.p',d5_funct_1)).

fof(f1215,plain,
    ( r2_hidden(k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl13_0 ),
    inference(unit_resulting_resolution,[],[f73,f74,f228,f137])).

fof(f137,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f76,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f1189,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f1188])).

fof(f1188,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f1187,f1043])).

fof(f1043,plain,
    ( r2_hidden(sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl13_1 ),
    inference(unit_resulting_resolution,[],[f144,f145,f76,f225,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK9(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f225,plain,
    ( ~ r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl13_1
  <=> ~ r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1187,plain,
    ( ~ r2_hidden(sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(forward_demodulation,[],[f1170,f1032])).

fof(f1032,plain,
    ( k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f1030,f387])).

fof(f387,plain,
    ( k1_funct_1(sK1,sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)))) = sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f73,f74,f234,f134])).

fof(f134,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f234,plain,
    ( r2_hidden(sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl13_2
  <=> r2_hidden(sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1030,plain,
    ( sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f251,f874])).

fof(f874,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)))
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f853,f387])).

fof(f853,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))))) = sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f144,f145,f386,f124])).

fof(f386,plain,
    ( r2_hidden(sK6(sK1,sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f73,f74,f234,f135])).

fof(f135,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f251,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl13_4
  <=> k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1170,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f73,f74,f225,f1031,f136])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1031,plain,
    ( r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f1030,f386])).

fof(f252,plain,
    ( spl13_0
    | spl13_4 ),
    inference(avatar_split_clause,[],[f239,f250,f227])).

fof(f239,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))) = sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0))
    | r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X2] :
      ( k10_relat_1(sK1,sK0) != X2
      | k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,X2)) = sK8(k2_funct_1(sK1),sK0,X2)
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X2),X2) ) ),
    inference(subsumption_resolution,[],[f174,f144])).

fof(f174,plain,(
    ! [X2] :
      ( k10_relat_1(sK1,sK0) != X2
      | k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,X2)) = sK8(k2_funct_1(sK1),sK0,X2)
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X2),X2)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f153,f145])).

fof(f153,plain,(
    ! [X2] :
      ( k10_relat_1(sK1,sK0) != X2
      | k1_funct_1(k2_funct_1(sK1),sK9(k2_funct_1(sK1),sK0,X2)) = sK8(k2_funct_1(sK1),sK0,X2)
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X2),X2)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f76,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,sK9(X0,X1,X2)) = sK8(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f235,plain,
    ( spl13_0
    | spl13_2 ),
    inference(avatar_split_clause,[],[f216,f233,f227])).

fof(f216,plain,
    ( r2_hidden(sK9(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | r2_hidden(sK8(k2_funct_1(sK1),sK0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,sK0) != X0
      | r2_hidden(sK9(k2_funct_1(sK1),sK0,X0),k2_relat_1(sK1))
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X0),X0) ) ),
    inference(backward_demodulation,[],[f183,f171])).

fof(f171,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,sK0) != X0
      | r2_hidden(sK9(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f170,f144])).

fof(f170,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,sK0) != X0
      | r2_hidden(sK9(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X0),X0)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f151,f145])).

fof(f151,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,sK0) != X0
      | r2_hidden(sK9(k2_funct_1(sK1),sK0,X0),k1_relat_1(k2_funct_1(sK1)))
      | r2_hidden(sK8(k2_funct_1(sK1),sK0,X0),X0)
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f76,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK8(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
