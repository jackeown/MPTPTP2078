%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t156_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:17 EDT 2019

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 578 expanded)
%              Number of leaves         :   13 ( 221 expanded)
%              Depth                    :   31
%              Number of atoms          :  442 (6148 expanded)
%              Number of equality atoms :  155 (2956 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26476,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f574,f26469])).

fof(f26469,plain,(
    ~ spl9_42 ),
    inference(avatar_contradiction_clause,[],[f26468])).

fof(f26468,plain,
    ( $false
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26467,f61])).

fof(f61,plain,(
    k1_relat_1(sK2) = sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( sK2 != sK3
    & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
    & k1_relat_1(sK3) = sK0
    & k1_relat_1(sK2) = sK0
    & k2_relat_1(sK1) = sK0
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
              & k1_relat_1(X3) = sK0
              & k1_relat_1(X2) = sK0
              & k2_relat_1(sK1) = sK0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( sK2 != X3
            & k5_relat_1(X1,sK2) = k5_relat_1(X1,X3)
            & k1_relat_1(X3) = X0
            & k1_relat_1(sK2) = X0
            & k2_relat_1(X1) = X0
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
          & k1_relat_1(X3) = X0
          & k1_relat_1(X2) = X0
          & k2_relat_1(X1) = X0
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( sK3 != X2
        & k5_relat_1(X1,sK3) = k5_relat_1(X1,X2)
        & k1_relat_1(sK3) = X0
        & k1_relat_1(X2) = X0
        & k2_relat_1(X1) = X0
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t156_funct_1.p',t156_funct_1)).

fof(f26467,plain,
    ( k1_relat_1(sK2) != sK0
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f26466,f62])).

fof(f62,plain,(
    k1_relat_1(sK3) = sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f26466,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26465,f56])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f26465,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26464,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f26464,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26463,f58])).

fof(f58,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f26463,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26462,f59])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f26462,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f26461,f64])).

fof(f64,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f26461,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(trivial_inequality_removal,[],[f26458])).

fof(f26458,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(superposition,[],[f68,f26438])).

fof(f26438,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f25944,f25942])).

fof(f25942,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3)))
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f25921,f56])).

fof(f25921,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3)))
    | ~ v1_relat_1(sK2)
    | ~ spl9_42 ),
    inference(resolution,[],[f582,f57])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,X0),sK7(sK1,sK4(sK2,sK3)))
        | ~ v1_relat_1(X0) )
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f581,f281])).

fof(f281,plain,(
    k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3))) = sK4(sK2,sK3) ),
    inference(resolution,[],[f280,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f92,f55])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f87,f60])).

fof(f60,plain,(
    k2_relat_1(sK1) = sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f50,f49,f48])).

fof(f48,plain,(
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
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t156_funct_1.p',d5_funct_1)).

fof(f280,plain,(
    r2_hidden(sK4(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f279,f58])).

fof(f279,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f278,f59])).

fof(f278,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f277,f64])).

fof(f277,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f113,f62])).

fof(f113,plain,(
    ! [X5] :
      ( k1_relat_1(X5) != sK0
      | r2_hidden(sK4(sK2,X5),sK0)
      | sK2 = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(forward_demodulation,[],[f112,f61])).

fof(f112,plain,(
    ! [X5] :
      ( k1_relat_1(X5) != sK0
      | r2_hidden(sK4(sK2,X5),k1_relat_1(sK2))
      | sK2 = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f111,f56])).

fof(f111,plain,(
    ! [X5] :
      ( k1_relat_1(X5) != sK0
      | r2_hidden(sK4(sK2,X5),k1_relat_1(sK2))
      | sK2 = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,(
    ! [X5] :
      ( k1_relat_1(X5) != sK0
      | r2_hidden(sK4(sK2,X5),k1_relat_1(sK2))
      | sK2 = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f67,f61])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t156_funct_1.p',t9_funct_1)).

fof(f581,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK1,X0),sK7(sK1,sK4(sK2,sK3)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f580,f54])).

fof(f580,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK1,X0),sK7(sK1,sK4(sK2,sK3)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f576,f55])).

fof(f576,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK1,X0),sK7(sK1,sK4(sK2,sK3)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_42 ),
    inference(resolution,[],[f561,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t156_funct_1.p',t23_funct_1)).

fof(f561,plain,
    ( r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl9_42
  <=> r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f25944,plain,
    ( k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3)))
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f25943,f63])).

fof(f63,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f25943,plain,
    ( k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK3),sK7(sK1,sK4(sK2,sK3)))
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f25922,f58])).

fof(f25922,plain,
    ( k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK3),sK7(sK1,sK4(sK2,sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl9_42 ),
    inference(resolution,[],[f582,f59])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f574,plain,(
    spl9_43 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f572,f280])).

fof(f572,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f571,f60])).

fof(f571,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK1))
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f570,f54])).

fof(f570,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f569,f55])).

fof(f569,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_43 ),
    inference(resolution,[],[f564,f88])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f564,plain,
    ( ~ r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl9_43
  <=> ~ r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
%------------------------------------------------------------------------------
