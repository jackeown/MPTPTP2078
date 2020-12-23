%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0098+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 (8638 expanded)
%              Number of leaves         :    6 (2393 expanded)
%              Depth                    :   29
%              Number of atoms          :  321 (37708 expanded)
%              Number of equality atoms :   16 (4018 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(subsumption_resolution,[],[f500,f446])).

fof(f446,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(subsumption_resolution,[],[f439,f380])).

fof(f380,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f379,f307])).

fof(f307,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(global_subsumption,[],[f174,f264,f306])).

fof(f306,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f305,f163])).

fof(f163,plain,(
    ~ sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f151,f162])).

fof(f162,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f151,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f142,f145])).

fof(f145,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2))
   => k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f140])).

fof(f140,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f139])).

fof(f139,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f305,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f240,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f158,f162])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f148,f149])).

fof(f149,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) )
     => ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f148,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f240,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f238,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f238,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f178,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f178,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f171,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f171,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f163,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f156,f162])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f264,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f263,f155])).

fof(f263,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f187,f153])).

fof(f187,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f172,f154])).

fof(f172,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f163,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f157,f162])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f174,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f163,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k5_xboole_0(X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f159,f162])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f379,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f378,f346])).

fof(f346,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
      | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),X0)
      | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,X0)) ) ),
    inference(resolution,[],[f308,f153])).

fof(f308,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(global_subsumption,[],[f213,f264,f276,f304])).

fof(f304,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f240,f155])).

fof(f276,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f274,f153])).

fof(f274,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f188,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f188,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f172,f155])).

fof(f213,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f174,f152])).

fof(f378,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f372,f163])).

fof(f372,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f329,f166])).

fof(f329,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f325,f154])).

fof(f325,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2)) ),
    inference(global_subsumption,[],[f172,f178,f214,f253,f276,f284,f294,f324])).

fof(f324,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f323,f153])).

fof(f323,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f322,f308])).

fof(f322,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f200,f240])).

fof(f200,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f173,f153])).

fof(f173,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f163,f165])).

fof(f294,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f292,f253])).

fof(f292,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f199,f152])).

fof(f199,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f173,f152])).

fof(f284,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f283,f154])).

fof(f283,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f278,f163])).

fof(f278,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f253,f164])).

fof(f253,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f230,f154])).

fof(f230,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(subsumption_resolution,[],[f229,f153])).

fof(f229,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f177,f152])).

fof(f177,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f171,f154])).

fof(f214,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f174,f153])).

fof(f439,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1) ),
    inference(resolution,[],[f413,f253])).

fof(f413,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f330,f380])).

fof(f330,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f325,f155])).

fof(f500,plain,(
    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(subsumption_resolution,[],[f494,f380])).

fof(f494,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f450,f152])).

fof(f450,plain,(
    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f449,f448])).

fof(f448,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(global_subsumption,[],[f326,f413,f446,f447])).

fof(f447,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f440,f163])).

fof(f440,plain,
    ( sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f413,f167])).

fof(f326,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),sK0) ),
    inference(resolution,[],[f325,f199])).

fof(f449,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f441,f163])).

fof(f441,plain,
    ( sQ4_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK1),sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f413,f165])).
%------------------------------------------------------------------------------
