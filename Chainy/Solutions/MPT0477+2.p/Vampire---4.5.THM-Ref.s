%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0477+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 157 expanded)
%              Number of leaves         :    7 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  236 ( 983 expanded)
%              Number of equality atoms :   76 ( 315 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1347,plain,(
    $false ),
    inference(subsumption_resolution,[],[f740,f1346])).

fof(f1346,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f1345,f1024])).

fof(f1024,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f1023,f764])).

fof(f764,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f1023,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f1020,f764])).

fof(f1020,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1019])).

fof(f1019,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f746,f979])).

fof(f979,plain,(
    ! [X0,X1] :
      ( sK1(k6_relat_1(X0),k6_relat_1(X1)) = sK2(k6_relat_1(X0),k6_relat_1(X1))
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f969,f775])).

fof(f775,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f769,f764])).

fof(f769,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f757])).

fof(f757,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f739])).

fof(f739,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK3(X0,X1) != sK4(X0,X1)
              | ~ r2_hidden(sK3(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( ( sK3(X0,X1) = sK4(X0,X1)
                & r2_hidden(sK3(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f737,f738])).

fof(f738,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK3(X0,X1) != sK4(X0,X1)
          | ~ r2_hidden(sK3(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( ( sK3(X0,X1) = sK4(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f737,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f736])).

fof(f736,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f735])).

fof(f735,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f728])).

fof(f728,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f969,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X0),k6_relat_1(X1)),sK1(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0))
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
      | sK1(k6_relat_1(X0),k6_relat_1(X1)) = sK2(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f863,f775])).

fof(f863,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X1))
      | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),k6_relat_1(X1)),sK1(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0))
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ) ),
    inference(resolution,[],[f815,f764])).

fof(f815,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK1(k6_relat_1(X0),X1),sK2(k6_relat_1(X0),X1)),X1)
      | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK1(k6_relat_1(X0),X1)),k6_relat_1(X0))
      | k4_relat_1(k6_relat_1(X0)) = X1 ) ),
    inference(resolution,[],[f745,f764])).

fof(f745,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | k4_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f734])).

fof(f734,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f732,f733])).

fof(f733,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f732,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f731])).

fof(f731,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f720])).

fof(f720,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f746,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f734])).

fof(f1345,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | r2_hidden(k4_tarski(sK1(k6_relat_1(X0),k6_relat_1(X0)),sK1(k6_relat_1(X0),k6_relat_1(X0))),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f1334,f776])).

fof(f776,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,X0)
      | r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f768,f764])).

fof(f768,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f767])).

fof(f767,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f758])).

fof(f758,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f739])).

fof(f1334,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k6_relat_1(X0),k6_relat_1(X0)),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(factoring,[],[f1278])).

fof(f1278,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k6_relat_1(X0),k6_relat_1(X1)),X0)
      | r2_hidden(sK1(k6_relat_1(X0),k6_relat_1(X1)),X1)
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f1277])).

fof(f1277,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k6_relat_1(X0),k6_relat_1(X1)),X0)
      | r2_hidden(sK1(k6_relat_1(X0),k6_relat_1(X1)),X1)
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ) ),
    inference(superposition,[],[f1080,f979])).

fof(f1080,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1(k6_relat_1(X4),k6_relat_1(X5)),X5)
      | r2_hidden(sK2(k6_relat_1(X4),k6_relat_1(X5)),X4)
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4)) ) ),
    inference(resolution,[],[f970,f774])).

fof(f774,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f770,f764])).

fof(f770,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f756])).

fof(f756,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f739])).

fof(f970,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X2))
      | k4_relat_1(k6_relat_1(X2)) = k6_relat_1(X3)
      | r2_hidden(sK1(k6_relat_1(X2),k6_relat_1(X3)),X3) ) ),
    inference(resolution,[],[f863,f774])).

fof(f740,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f730])).

fof(f730,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f718,f729])).

fof(f729,plain,
    ( ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f718,plain,(
    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f717])).

fof(f717,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f716])).

fof(f716,conjecture,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
%------------------------------------------------------------------------------
