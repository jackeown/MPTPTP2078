%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0792+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 17.53s
% Output     : Refutation 17.89s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 142 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   20
%              Number of atoms          :  350 (1069 expanded)
%              Number of equality atoms :   64 ( 148 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6996,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6995,f3225])).

fof(f3225,plain,(
    v1_relat_1(sK41) ),
    inference(cnf_transformation,[],[f2420])).

fof(f2420,plain,
    ( ~ r2_hidden(k4_tarski(sK39,sK40),sK41)
    & ! [X3] :
        ( ( sK40 != X3
          & r2_hidden(k4_tarski(X3,sK40),sK41) )
        | ~ r2_hidden(X3,k1_wellord1(sK41,sK39)) )
    & r2_hidden(sK40,k3_relat_1(sK41))
    & r2_hidden(sK39,k3_relat_1(sK41))
    & v2_wellord1(sK41)
    & v1_relat_1(sK41) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39,sK40,sK41])],[f1203,f2419])).

fof(f2419,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        & ! [X3] :
            ( ( X1 != X3
              & r2_hidden(k4_tarski(X3,X1),X2) )
            | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k4_tarski(sK39,sK40),sK41)
      & ! [X3] :
          ( ( sK40 != X3
            & r2_hidden(k4_tarski(X3,sK40),sK41) )
          | ~ r2_hidden(X3,k1_wellord1(sK41,sK39)) )
      & r2_hidden(sK40,k3_relat_1(sK41))
      & r2_hidden(sK39,k3_relat_1(sK41))
      & v2_wellord1(sK41)
      & v1_relat_1(sK41) ) ),
    introduced(choice_axiom,[])).

fof(f1203,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1202])).

fof(f1202,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1177])).

fof(f1177,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1176])).

fof(f1176,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_wellord1)).

fof(f6995,plain,(
    ~ v1_relat_1(sK41) ),
    inference(subsumption_resolution,[],[f6991,f3226])).

fof(f3226,plain,(
    v2_wellord1(sK41) ),
    inference(cnf_transformation,[],[f2420])).

fof(f6991,plain,
    ( ~ v2_wellord1(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(resolution,[],[f6917,f3448])).

fof(f3448,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f2474,plain,(
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
    inference(flattening,[],[f2473])).

fof(f2473,plain,(
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
    inference(nnf_transformation,[],[f1301])).

fof(f1301,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f6917,plain,(
    ~ v1_relat_2(sK41) ),
    inference(subsumption_resolution,[],[f6916,f3225])).

fof(f6916,plain,
    ( ~ v1_relat_2(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(subsumption_resolution,[],[f6872,f3227])).

fof(f3227,plain,(
    r2_hidden(sK39,k3_relat_1(sK41)) ),
    inference(cnf_transformation,[],[f2420])).

fof(f6872,plain,
    ( ~ r2_hidden(sK39,k3_relat_1(sK41))
    | ~ v1_relat_2(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(resolution,[],[f6654,f3426])).

fof(f3426,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2455])).

fof(f2455,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK54(X0),sK54(X0)),X0)
            & r2_hidden(sK54(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54])],[f2453,f2454])).

fof(f2454,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK54(X0),sK54(X0)),X0)
        & r2_hidden(sK54(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2453,plain,(
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
    inference(rectify,[],[f2452])).

fof(f2452,plain,(
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
    inference(nnf_transformation,[],[f1294])).

fof(f1294,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1141])).

fof(f1141,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f6654,plain,(
    ~ r2_hidden(k4_tarski(sK39,sK39),sK41) ),
    inference(backward_demodulation,[],[f3231,f6651])).

fof(f6651,plain,(
    sK39 = sK40 ),
    inference(subsumption_resolution,[],[f6650,f3225])).

fof(f6650,plain,
    ( sK39 = sK40
    | ~ v1_relat_1(sK41) ),
    inference(subsumption_resolution,[],[f6644,f3226])).

fof(f6644,plain,
    ( sK39 = sK40
    | ~ v2_wellord1(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(resolution,[],[f5798,f3451])).

fof(f3451,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f5798,plain,
    ( ~ v6_relat_2(sK41)
    | sK39 = sK40 ),
    inference(subsumption_resolution,[],[f5751,f5797])).

fof(f5797,plain,
    ( ~ r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40 ),
    inference(subsumption_resolution,[],[f5763,f3225])).

fof(f5763,plain,
    ( ~ r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40
    | ~ v1_relat_1(sK41) ),
    inference(resolution,[],[f5248,f5261])).

fof(f5261,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3555])).

fof(f3555,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2527])).

fof(f2527,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK83(X0,X1,X2),X1),X0)
                | sK83(X0,X1,X2) = X1
                | ~ r2_hidden(sK83(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK83(X0,X1,X2),X1),X0)
                  & sK83(X0,X1,X2) != X1 )
                | r2_hidden(sK83(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK83])],[f2525,f2526])).

fof(f2526,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK83(X0,X1,X2),X1),X0)
          | sK83(X0,X1,X2) = X1
          | ~ r2_hidden(sK83(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK83(X0,X1,X2),X1),X0)
            & sK83(X0,X1,X2) != X1 )
          | r2_hidden(sK83(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2525,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2524])).

fof(f2524,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2523])).

fof(f2523,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1376])).

fof(f1376,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1130])).

fof(f1130,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f5248,plain,(
    ~ r2_hidden(sK40,k1_wellord1(sK41,sK39)) ),
    inference(equality_resolution,[],[f3230])).

fof(f3230,plain,(
    ! [X3] :
      ( sK40 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK41,sK39)) ) ),
    inference(cnf_transformation,[],[f2420])).

fof(f5751,plain,
    ( r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40
    | ~ v6_relat_2(sK41) ),
    inference(subsumption_resolution,[],[f5750,f3225])).

fof(f5750,plain,
    ( r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40
    | ~ v6_relat_2(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(subsumption_resolution,[],[f5749,f3227])).

fof(f5749,plain,
    ( r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40
    | ~ r2_hidden(sK39,k3_relat_1(sK41))
    | ~ v6_relat_2(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(subsumption_resolution,[],[f5705,f3228])).

fof(f3228,plain,(
    r2_hidden(sK40,k3_relat_1(sK41)) ),
    inference(cnf_transformation,[],[f2420])).

fof(f5705,plain,
    ( r2_hidden(k4_tarski(sK40,sK39),sK41)
    | sK39 = sK40
    | ~ r2_hidden(sK40,k3_relat_1(sK41))
    | ~ r2_hidden(sK39,k3_relat_1(sK41))
    | ~ v6_relat_2(sK41)
    | ~ v1_relat_1(sK41) ),
    inference(resolution,[],[f3231,f3438])).

fof(f3438,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X4,X3),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2468])).

fof(f2468,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK60(X0),sK59(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK59(X0),sK60(X0)),X0)
            & sK59(X0) != sK60(X0)
            & r2_hidden(sK60(X0),k3_relat_1(X0))
            & r2_hidden(sK59(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK59,sK60])],[f2466,f2467])).

fof(f2467,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK60(X0),sK59(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK59(X0),sK60(X0)),X0)
        & sK59(X0) != sK60(X0)
        & r2_hidden(sK60(X0),k3_relat_1(X0))
        & r2_hidden(sK59(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2466,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2465])).

fof(f2465,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1298])).

fof(f1298,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1145])).

fof(f1145,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f3231,plain,(
    ~ r2_hidden(k4_tarski(sK39,sK40),sK41) ),
    inference(cnf_transformation,[],[f2420])).
%------------------------------------------------------------------------------
