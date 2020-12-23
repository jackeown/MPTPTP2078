%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:51 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 321 expanded)
%              Number of equality atoms :   59 (  84 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f24])).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f199,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f58,f173])).

fof(f173,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k1_tarski(X2),X3) = X3
      | ~ r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X3)
      | k2_xboole_0(k1_tarski(X2),X3) = X3
      | k2_xboole_0(k1_tarski(X2),X3) = X3 ) ),
    inference(superposition,[],[f42,f106])).

fof(f106,plain,(
    ! [X2,X3] :
      ( sK3(k1_tarski(X2),X3,X3) = X2
      | k2_xboole_0(k1_tarski(X2),X3) = X3 ) ),
    inference(resolution,[],[f102,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | r2_hidden(sK3(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f49,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:43:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (1225392128)
% 0.15/0.37  ipcrm: permission denied for id (1226506241)
% 0.15/0.38  ipcrm: permission denied for id (1226571779)
% 0.15/0.38  ipcrm: permission denied for id (1226604548)
% 0.15/0.38  ipcrm: permission denied for id (1226637317)
% 0.15/0.38  ipcrm: permission denied for id (1226670086)
% 0.15/0.38  ipcrm: permission denied for id (1230143495)
% 0.15/0.38  ipcrm: permission denied for id (1226735624)
% 0.15/0.38  ipcrm: permission denied for id (1225424905)
% 0.15/0.38  ipcrm: permission denied for id (1226768394)
% 0.15/0.39  ipcrm: permission denied for id (1225490443)
% 0.15/0.39  ipcrm: permission denied for id (1230176268)
% 0.15/0.39  ipcrm: permission denied for id (1226833933)
% 0.15/0.39  ipcrm: permission denied for id (1230209038)
% 0.15/0.39  ipcrm: permission denied for id (1226899471)
% 0.15/0.39  ipcrm: permission denied for id (1226932240)
% 0.15/0.39  ipcrm: permission denied for id (1230241809)
% 0.15/0.39  ipcrm: permission denied for id (1226997778)
% 0.15/0.40  ipcrm: permission denied for id (1227030547)
% 0.15/0.40  ipcrm: permission denied for id (1230274580)
% 0.22/0.40  ipcrm: permission denied for id (1227096085)
% 0.22/0.40  ipcrm: permission denied for id (1230307350)
% 0.22/0.40  ipcrm: permission denied for id (1230340119)
% 0.22/0.41  ipcrm: permission denied for id (1227292699)
% 0.22/0.41  ipcrm: permission denied for id (1225588764)
% 0.22/0.41  ipcrm: permission denied for id (1230471197)
% 0.22/0.41  ipcrm: permission denied for id (1227358238)
% 0.22/0.41  ipcrm: permission denied for id (1227391007)
% 0.22/0.41  ipcrm: permission denied for id (1230503968)
% 0.22/0.41  ipcrm: permission denied for id (1227489314)
% 0.22/0.42  ipcrm: permission denied for id (1230602276)
% 0.22/0.42  ipcrm: permission denied for id (1225654309)
% 0.22/0.42  ipcrm: permission denied for id (1227587622)
% 0.22/0.42  ipcrm: permission denied for id (1232437287)
% 0.22/0.42  ipcrm: permission denied for id (1230667816)
% 0.22/0.42  ipcrm: permission denied for id (1230700585)
% 0.22/0.42  ipcrm: permission denied for id (1232470058)
% 0.22/0.43  ipcrm: permission denied for id (1227751467)
% 0.22/0.43  ipcrm: permission denied for id (1227849774)
% 0.22/0.43  ipcrm: permission denied for id (1232568367)
% 0.22/0.43  ipcrm: permission denied for id (1230897201)
% 0.22/0.43  ipcrm: permission denied for id (1225687090)
% 0.22/0.44  ipcrm: permission denied for id (1225719859)
% 0.22/0.44  ipcrm: permission denied for id (1230929972)
% 0.22/0.44  ipcrm: permission denied for id (1230962741)
% 0.22/0.44  ipcrm: permission denied for id (1228046390)
% 0.22/0.44  ipcrm: permission denied for id (1230995511)
% 0.22/0.44  ipcrm: permission denied for id (1228111928)
% 0.22/0.44  ipcrm: permission denied for id (1231028281)
% 0.22/0.44  ipcrm: permission denied for id (1225752634)
% 0.22/0.45  ipcrm: permission denied for id (1225785403)
% 0.22/0.45  ipcrm: permission denied for id (1231061052)
% 0.22/0.45  ipcrm: permission denied for id (1231093821)
% 0.22/0.45  ipcrm: permission denied for id (1231126590)
% 0.22/0.45  ipcrm: permission denied for id (1225818175)
% 0.22/0.45  ipcrm: permission denied for id (1231159360)
% 0.22/0.45  ipcrm: permission denied for id (1225850945)
% 0.22/0.45  ipcrm: permission denied for id (1232633922)
% 0.22/0.45  ipcrm: permission denied for id (1232666691)
% 0.22/0.46  ipcrm: permission denied for id (1232699460)
% 0.22/0.46  ipcrm: permission denied for id (1228406853)
% 0.22/0.46  ipcrm: permission denied for id (1231290438)
% 0.22/0.46  ipcrm: permission denied for id (1228472391)
% 0.22/0.46  ipcrm: permission denied for id (1231323208)
% 0.22/0.46  ipcrm: permission denied for id (1231355977)
% 0.22/0.46  ipcrm: permission denied for id (1228570698)
% 0.22/0.47  ipcrm: permission denied for id (1232765004)
% 0.22/0.47  ipcrm: permission denied for id (1231454285)
% 0.22/0.47  ipcrm: permission denied for id (1228701774)
% 0.22/0.47  ipcrm: permission denied for id (1228734543)
% 0.22/0.47  ipcrm: permission denied for id (1232797776)
% 0.22/0.47  ipcrm: permission denied for id (1228800081)
% 0.22/0.47  ipcrm: permission denied for id (1232830546)
% 0.22/0.47  ipcrm: permission denied for id (1231552595)
% 0.22/0.48  ipcrm: permission denied for id (1225982036)
% 0.22/0.48  ipcrm: permission denied for id (1231585365)
% 0.22/0.48  ipcrm: permission denied for id (1231618134)
% 0.22/0.48  ipcrm: permission denied for id (1228963927)
% 0.22/0.48  ipcrm: permission denied for id (1228996696)
% 0.22/0.48  ipcrm: permission denied for id (1229029465)
% 0.22/0.48  ipcrm: permission denied for id (1229062234)
% 0.22/0.48  ipcrm: permission denied for id (1229095003)
% 0.22/0.49  ipcrm: permission denied for id (1231650908)
% 0.22/0.49  ipcrm: permission denied for id (1232863325)
% 0.22/0.49  ipcrm: permission denied for id (1232896094)
% 0.22/0.49  ipcrm: permission denied for id (1229226079)
% 0.22/0.49  ipcrm: permission denied for id (1232928864)
% 0.22/0.49  ipcrm: permission denied for id (1231781985)
% 0.22/0.49  ipcrm: permission denied for id (1232961634)
% 0.22/0.49  ipcrm: permission denied for id (1229357155)
% 0.22/0.50  ipcrm: permission denied for id (1229389924)
% 0.22/0.50  ipcrm: permission denied for id (1233027174)
% 0.22/0.50  ipcrm: permission denied for id (1231913063)
% 0.22/0.50  ipcrm: permission denied for id (1231945832)
% 0.22/0.50  ipcrm: permission denied for id (1229553769)
% 0.22/0.50  ipcrm: permission denied for id (1229586538)
% 0.22/0.50  ipcrm: permission denied for id (1226178667)
% 0.22/0.51  ipcrm: permission denied for id (1229619308)
% 0.22/0.51  ipcrm: permission denied for id (1229684846)
% 0.22/0.51  ipcrm: permission denied for id (1229717615)
% 0.22/0.51  ipcrm: permission denied for id (1226244208)
% 0.22/0.51  ipcrm: permission denied for id (1226276977)
% 0.22/0.51  ipcrm: permission denied for id (1229750386)
% 0.22/0.51  ipcrm: permission denied for id (1229783155)
% 0.22/0.52  ipcrm: permission denied for id (1226342516)
% 0.22/0.52  ipcrm: permission denied for id (1232011381)
% 0.22/0.52  ipcrm: permission denied for id (1233125495)
% 0.22/0.52  ipcrm: permission denied for id (1229914232)
% 0.22/0.52  ipcrm: permission denied for id (1229947001)
% 0.22/0.52  ipcrm: permission denied for id (1233158266)
% 0.22/0.52  ipcrm: permission denied for id (1230012539)
% 0.22/0.52  ipcrm: permission denied for id (1230045308)
% 0.22/0.53  ipcrm: permission denied for id (1226440829)
% 0.22/0.53  ipcrm: permission denied for id (1233191038)
% 0.22/0.53  ipcrm: permission denied for id (1226473599)
% 1.19/0.67  % (26945)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.70  % (26952)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.71  % (26964)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.71  % (26960)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.71  % (26960)Refutation not found, incomplete strategy% (26960)------------------------------
% 1.38/0.71  % (26960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.71  % (26960)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.71  
% 1.38/0.71  % (26960)Memory used [KB]: 1663
% 1.38/0.71  % (26960)Time elapsed: 0.143 s
% 1.38/0.71  % (26960)------------------------------
% 1.38/0.71  % (26960)------------------------------
% 1.38/0.72  % (26968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.72  % (26952)Refutation found. Thanks to Tanya!
% 1.66/0.72  % SZS status Theorem for theBenchmark
% 1.66/0.72  % SZS output start Proof for theBenchmark
% 1.66/0.72  fof(f200,plain,(
% 1.66/0.72    $false),
% 1.66/0.72    inference(subsumption_resolution,[],[f199,f24])).
% 1.66/0.72  fof(f24,plain,(
% 1.66/0.72    r2_hidden(sK0,sK1)),
% 1.66/0.72    inference(cnf_transformation,[],[f14])).
% 1.66/0.72  fof(f14,plain,(
% 1.66/0.72    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.66/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 1.66/0.72  fof(f13,plain,(
% 1.66/0.72    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.66/0.72    introduced(choice_axiom,[])).
% 1.66/0.72  fof(f12,plain,(
% 1.66/0.72    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.66/0.72    inference(ennf_transformation,[],[f11])).
% 1.66/0.72  fof(f11,negated_conjecture,(
% 1.66/0.72    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.72    inference(negated_conjecture,[],[f10])).
% 1.66/0.72  fof(f10,conjecture,(
% 1.66/0.72    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.66/0.72  fof(f199,plain,(
% 1.66/0.72    ~r2_hidden(sK0,sK1)),
% 1.66/0.72    inference(trivial_inequality_removal,[],[f188])).
% 1.66/0.72  fof(f188,plain,(
% 1.66/0.72    sK1 != sK1 | ~r2_hidden(sK0,sK1)),
% 1.66/0.72    inference(superposition,[],[f58,f173])).
% 1.66/0.72  fof(f173,plain,(
% 1.66/0.72    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X2),X3) = X3 | ~r2_hidden(X2,X3)) )),
% 1.66/0.72    inference(duplicate_literal_removal,[],[f166])).
% 1.66/0.72  fof(f166,plain,(
% 1.66/0.72    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X2,X3) | k2_xboole_0(k1_tarski(X2),X3) = X3 | k2_xboole_0(k1_tarski(X2),X3) = X3) )),
% 1.66/0.72    inference(superposition,[],[f42,f106])).
% 1.66/0.72  fof(f106,plain,(
% 1.66/0.72    ( ! [X2,X3] : (sK3(k1_tarski(X2),X3,X3) = X2 | k2_xboole_0(k1_tarski(X2),X3) = X3) )),
% 1.66/0.72    inference(resolution,[],[f102,f45])).
% 1.66/0.72  fof(f45,plain,(
% 1.66/0.72    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.66/0.72    inference(equality_resolution,[],[f32])).
% 1.66/0.72  fof(f32,plain,(
% 1.66/0.72    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.66/0.72    inference(cnf_transformation,[],[f18])).
% 1.66/0.72  fof(f18,plain,(
% 1.66/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 1.66/0.72  fof(f17,plain,(
% 1.66/0.72    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.66/0.72    introduced(choice_axiom,[])).
% 1.66/0.72  fof(f16,plain,(
% 1.66/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.72    inference(rectify,[],[f15])).
% 1.66/0.72  fof(f15,plain,(
% 1.66/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.72    inference(nnf_transformation,[],[f6])).
% 1.66/0.72  fof(f6,axiom,(
% 1.66/0.72    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.66/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.66/0.72  fof(f102,plain,(
% 1.66/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 1.66/0.72    inference(subsumption_resolution,[],[f98,f42])).
% 1.66/0.72  fof(f98,plain,(
% 1.66/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 1.66/0.72    inference(factoring,[],[f40])).
% 1.66/0.72  fof(f40,plain,(
% 1.66/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 1.66/0.72    inference(cnf_transformation,[],[f23])).
% 1.66/0.72  fof(f23,plain,(
% 1.66/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.66/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.66/0.72  fof(f22,plain,(
% 1.66/0.72    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.66/0.72    introduced(choice_axiom,[])).
% 1.66/0.72  fof(f21,plain,(
% 1.66/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.66/0.72    inference(rectify,[],[f20])).
% 1.66/0.72  fof(f20,plain,(
% 1.66/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.66/0.72    inference(flattening,[],[f19])).
% 1.66/0.72  fof(f19,plain,(
% 1.66/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.66/0.72    inference(nnf_transformation,[],[f2])).
% 1.66/0.72  fof(f2,axiom,(
% 1.66/0.72    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.66/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.66/0.72  fof(f42,plain,(
% 1.66/0.72    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 1.66/0.72    inference(cnf_transformation,[],[f23])).
% 1.66/0.72  fof(f58,plain,(
% 1.66/0.72    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.66/0.72    inference(superposition,[],[f49,f31])).
% 1.66/0.72  fof(f31,plain,(
% 1.66/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.72    inference(cnf_transformation,[],[f4])).
% 1.66/0.72  fof(f4,axiom,(
% 1.66/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.66/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.66/0.72  fof(f49,plain,(
% 1.66/0.72    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 1.66/0.72    inference(superposition,[],[f25,f27])).
% 1.66/0.72  fof(f27,plain,(
% 1.66/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.66/0.72    inference(cnf_transformation,[],[f1])).
% 1.66/0.72  fof(f1,axiom,(
% 1.66/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.66/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.66/0.72  fof(f25,plain,(
% 1.66/0.72    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.66/0.72    inference(cnf_transformation,[],[f14])).
% 1.66/0.72  % SZS output end Proof for theBenchmark
% 1.66/0.72  % (26952)------------------------------
% 1.66/0.72  % (26952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.72  % (26952)Termination reason: Refutation
% 1.66/0.72  
% 1.66/0.72  % (26952)Memory used [KB]: 1791
% 1.66/0.72  % (26952)Time elapsed: 0.164 s
% 1.66/0.72  % (26952)------------------------------
% 1.66/0.72  % (26952)------------------------------
% 1.66/0.73  % (26805)Success in time 0.358 s
%------------------------------------------------------------------------------
