%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0766+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   36 (  98 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 ( 934 expanded)
%              Number of equality atoms :   12 (  84 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6576,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6575,f3075])).

fof(f3075,plain,(
    v1_relat_1(sK20) ),
    inference(cnf_transformation,[],[f2316])).

fof(f2316,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK22(X2)),sK20)
          & sK21 != sK22(X2)
          & r2_hidden(k4_tarski(sK21,sK22(X2)),sK20)
          & r2_hidden(sK22(X2),k3_relat_1(sK20)) )
        | ~ r2_hidden(k4_tarski(sK21,X2),sK20)
        | ~ r2_hidden(X2,k3_relat_1(sK20)) )
    & ~ r2_hidden(k4_tarski(sK23,sK21),sK20)
    & r2_hidden(sK23,k3_relat_1(sK20))
    & r2_hidden(sK21,k3_relat_1(sK20))
    & v2_wellord1(sK20)
    & v1_relat_1(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22,sK23])],[f1175,f2315,f2314,f2313,f2312])).

fof(f2312,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & X1 != X3
                    & r2_hidden(k4_tarski(X1,X3),X0)
                    & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X1,X2),X0)
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & ? [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                & r2_hidden(X4,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK20)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK20)
                  & r2_hidden(X3,k3_relat_1(sK20)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK20)
              | ~ r2_hidden(X2,k3_relat_1(sK20)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK20)
              & r2_hidden(X4,k3_relat_1(sK20)) )
          & r2_hidden(X1,k3_relat_1(sK20)) )
      & v2_wellord1(sK20)
      & v1_relat_1(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f2313,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),sK20)
                & X1 != X3
                & r2_hidden(k4_tarski(X1,X3),sK20)
                & r2_hidden(X3,k3_relat_1(sK20)) )
            | ~ r2_hidden(k4_tarski(X1,X2),sK20)
            | ~ r2_hidden(X2,k3_relat_1(sK20)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),sK20)
            & r2_hidden(X4,k3_relat_1(sK20)) )
        & r2_hidden(X1,k3_relat_1(sK20)) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k4_tarski(X2,X3),sK20)
              & sK21 != X3
              & r2_hidden(k4_tarski(sK21,X3),sK20)
              & r2_hidden(X3,k3_relat_1(sK20)) )
          | ~ r2_hidden(k4_tarski(sK21,X2),sK20)
          | ~ r2_hidden(X2,k3_relat_1(sK20)) )
      & ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK21),sK20)
          & r2_hidden(X4,k3_relat_1(sK20)) )
      & r2_hidden(sK21,k3_relat_1(sK20)) ) ),
    introduced(choice_axiom,[])).

fof(f2314,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),sK20)
          & sK21 != X3
          & r2_hidden(k4_tarski(sK21,X3),sK20)
          & r2_hidden(X3,k3_relat_1(sK20)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK22(X2)),sK20)
        & sK21 != sK22(X2)
        & r2_hidden(k4_tarski(sK21,sK22(X2)),sK20)
        & r2_hidden(sK22(X2),k3_relat_1(sK20)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2315,plain,
    ( ? [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK21),sK20)
        & r2_hidden(X4,k3_relat_1(sK20)) )
   => ( ~ r2_hidden(k4_tarski(sK23,sK21),sK20)
      & r2_hidden(sK23,k3_relat_1(sK20)) ) ),
    introduced(choice_axiom,[])).

fof(f1175,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1174])).

fof(f1174,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1151])).

fof(f1151,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f1146])).

fof(f1146,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1145])).

fof(f1145,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).

fof(f6575,plain,(
    ~ v1_relat_1(sK20) ),
    inference(subsumption_resolution,[],[f6574,f6250])).

fof(f6250,plain,(
    v1_relat_2(sK20) ),
    inference(subsumption_resolution,[],[f6245,f3075])).

fof(f6245,plain,
    ( v1_relat_2(sK20)
    | ~ v1_relat_1(sK20) ),
    inference(resolution,[],[f3076,f3289])).

fof(f3289,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2362])).

fof(f2362,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2361])).

fof(f2361,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1266])).

fof(f1266,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f3076,plain,(
    v2_wellord1(sK20) ),
    inference(cnf_transformation,[],[f2316])).

fof(f6574,plain,
    ( ~ v1_relat_2(sK20)
    | ~ v1_relat_1(sK20) ),
    inference(subsumption_resolution,[],[f6564,f3077])).

fof(f3077,plain,(
    r2_hidden(sK21,k3_relat_1(sK20)) ),
    inference(cnf_transformation,[],[f2316])).

fof(f6564,plain,
    ( ~ r2_hidden(sK21,k3_relat_1(sK20))
    | ~ v1_relat_2(sK20)
    | ~ v1_relat_1(sK20) ),
    inference(resolution,[],[f6551,f3271])).

fof(f3271,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2347])).

fof(f2347,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK34(X0),sK34(X0)),X0)
            & r2_hidden(sK34(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34])],[f2345,f2346])).

fof(f2346,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK34(X0),sK34(X0)),X0)
        & r2_hidden(sK34(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2345,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2344])).

fof(f2344,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1261])).

fof(f1261,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1139])).

fof(f1139,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f6551,plain,(
    ~ r2_hidden(k4_tarski(sK21,sK21),sK20) ),
    inference(subsumption_resolution,[],[f6550,f3077])).

fof(f6550,plain,
    ( ~ r2_hidden(k4_tarski(sK21,sK21),sK20)
    | ~ r2_hidden(sK21,k3_relat_1(sK20)) ),
    inference(duplicate_literal_removal,[],[f6538])).

fof(f6538,plain,
    ( ~ r2_hidden(k4_tarski(sK21,sK21),sK20)
    | ~ r2_hidden(sK21,k3_relat_1(sK20))
    | ~ r2_hidden(k4_tarski(sK21,sK21),sK20)
    | ~ r2_hidden(sK21,k3_relat_1(sK20)) ),
    inference(resolution,[],[f3083,f3081])).

fof(f3081,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK21,sK22(X2)),sK20)
      | ~ r2_hidden(k4_tarski(sK21,X2),sK20)
      | ~ r2_hidden(X2,k3_relat_1(sK20)) ) ),
    inference(cnf_transformation,[],[f2316])).

fof(f3083,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK22(X2)),sK20)
      | ~ r2_hidden(k4_tarski(sK21,X2),sK20)
      | ~ r2_hidden(X2,k3_relat_1(sK20)) ) ),
    inference(cnf_transformation,[],[f2316])).
%------------------------------------------------------------------------------
