%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0182+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 225 expanded)
%              Number of leaves         :    5 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 (1581 expanded)
%              Number of equality atoms :  139 (1226 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f985,plain,(
    $false ),
    inference(subsumption_resolution,[],[f984,f704])).

fof(f704,plain,(
    r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f703,f647])).

fof(f647,plain,(
    sK0 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f646,f370])).

fof(f370,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f246])).

fof(f246,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f646,plain,(
    sK0 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f577,f370,f639])).

fof(f639,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | sK0 != sK3(sK1,sK0,sK2,X2)
      | k1_enumset1(sK0,sK1,sK2) != X2 ) ),
    inference(inner_rewriting,[],[f636])).

fof(f636,plain,(
    ! [X2] :
      ( k1_enumset1(sK0,sK1,sK2) != X2
      | sK0 != sK3(sK1,sK0,sK2,X2)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X2),X2) ) ),
    inference(superposition,[],[f336,f359])).

fof(f359,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f286])).

% (19926)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f286,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f284,f285])).

fof(f285,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f284,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f283])).

fof(f283,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f282])).

fof(f282,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f253])).

fof(f253,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f174])).

fof(f174,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f336,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f281])).

fof(f281,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f252,f280])).

fof(f280,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f252,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f248])).

fof(f248,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f247])).

fof(f247,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f577,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f576])).

fof(f576,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f354])).

fof(f354,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f703,plain,
    ( sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f702,f651])).

fof(f651,plain,(
    sK2 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f650,f370])).

fof(f650,plain,(
    sK2 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f575,f370,f640])).

fof(f640,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | sK2 != sK3(sK1,sK0,sK2,X3)
      | k1_enumset1(sK0,sK1,sK2) != X3 ) ),
    inference(inner_rewriting,[],[f637])).

fof(f637,plain,(
    ! [X3] :
      ( k1_enumset1(sK0,sK1,sK2) != X3
      | sK2 != sK3(sK1,sK0,sK2,X3)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X3),X3) ) ),
    inference(superposition,[],[f336,f360])).

fof(f360,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f286])).

fof(f575,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f574])).

fof(f574,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f355])).

fof(f355,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f702,plain,
    ( sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f698,f336])).

fof(f698,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2)
    | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f695])).

fof(f695,plain,
    ( sK1 != sK1
    | k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2)
    | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f643,f357])).

fof(f357,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f286])).

fof(f643,plain,(
    sK1 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f642,f370])).

fof(f642,plain,(
    sK1 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f573,f370,f638])).

fof(f638,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | sK1 != sK3(sK1,sK0,sK2,X1)
      | k1_enumset1(sK0,sK1,sK2) != X1 ) ),
    inference(inner_rewriting,[],[f635])).

fof(f635,plain,(
    ! [X1] :
      ( k1_enumset1(sK0,sK1,sK2) != X1
      | sK1 != sK3(sK1,sK0,sK2,X1)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X1),X1) ) ),
    inference(superposition,[],[f336,f358])).

fof(f358,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f286])).

fof(f573,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f572])).

fof(f572,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f356])).

fof(f356,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f984,plain,(
    ~ r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f912,f370])).

fof(f912,plain,(
    ~ r2_hidden(sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f643,f647,f651,f578])).

fof(f578,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f353])).

fof(f353,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f286])).
%------------------------------------------------------------------------------
