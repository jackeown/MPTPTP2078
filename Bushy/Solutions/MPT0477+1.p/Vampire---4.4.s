%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t72_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 342 expanded)
%              Number of leaves         :    9 (  83 expanded)
%              Depth                    :   25
%              Number of atoms          :  307 (2088 expanded)
%              Number of equality atoms :  100 ( 662 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3645,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f3408])).

fof(f3408,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f3402])).

fof(f3402,plain,
    ( $false
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f112,f3106])).

fof(f3106,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f3104,f2143])).

fof(f2143,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK6(X2,k4_relat_1(k6_relat_1(X2))),sK6(X2,k4_relat_1(k6_relat_1(X2)))),k4_relat_1(k6_relat_1(X2)))
      | k6_relat_1(X2) = k4_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f2138,f52])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',dt_k6_relat_1)).

fof(f2138,plain,(
    ! [X2] :
      ( k6_relat_1(X2) = k4_relat_1(k6_relat_1(X2))
      | r2_hidden(k4_tarski(sK6(X2,k4_relat_1(k6_relat_1(X2))),sK6(X2,k4_relat_1(k6_relat_1(X2)))),k4_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f1597,f126])).

fof(f126,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',dt_k4_relat_1)).

fof(f78,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',d7_relat_1)).

fof(f1597,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK6(X1,k4_relat_1(k6_relat_1(X1))),sK6(X1,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
      | k6_relat_1(X1) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f1584,f121])).

fof(f121,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,X0)
      | r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f81,f52])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK6(X0,X1) != sK7(X0,X1)
              | ~ r2_hidden(sK6(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
            & ( ( sK6(X0,X1) = sK7(X0,X1)
                & r2_hidden(sK6(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK6(X0,X1) != sK7(X0,X1)
          | ~ r2_hidden(sK6(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( ( sK6(X0,X1) = sK7(X0,X1)
            & r2_hidden(sK6(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',d10_relat_1)).

fof(f1584,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X0))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(factoring,[],[f840])).

fof(f840,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X1)
      | r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f839])).

fof(f839,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X1)
      | r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f448,f256])).

fof(f256,plain,(
    ! [X0,X1] :
      ( sK6(X0,k4_relat_1(k6_relat_1(X1))) = sK7(X0,k4_relat_1(k6_relat_1(X1)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f255,f124])).

fof(f124,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f82,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f255,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | sK6(X0,k4_relat_1(k6_relat_1(X1))) = sK7(X0,k4_relat_1(k6_relat_1(X1)))
      | r2_hidden(k4_tarski(sK7(X0,k4_relat_1(k6_relat_1(X1))),sK6(X0,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f250,f52])).

fof(f250,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | sK6(X0,k4_relat_1(k6_relat_1(X1))) = sK7(X0,k4_relat_1(k6_relat_1(X1)))
      | r2_hidden(k4_tarski(sK7(X0,k4_relat_1(k6_relat_1(X1))),sK6(X0,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f175,f136])).

fof(f136,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X1))),sK7(X0,k4_relat_1(k6_relat_1(X1)))),k4_relat_1(k6_relat_1(X1)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | sK6(X0,k4_relat_1(k6_relat_1(X1))) = sK7(X0,k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f144,f52])).

fof(f144,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK6(X2,k4_relat_1(X3)),sK7(X2,k4_relat_1(X3))),k4_relat_1(X3))
      | k6_relat_1(X2) = k4_relat_1(X3)
      | sK6(X2,k4_relat_1(X3)) = sK7(X2,k4_relat_1(X3)) ) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sK6(X0,X1) = sK7(X0,X1)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f448,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0)
      | r2_hidden(sK7(X0,k4_relat_1(k6_relat_1(X1))),X1)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f238,f125])).

fof(f125,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f83,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,k4_relat_1(k6_relat_1(X1))),sK6(X0,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
      | r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f233,f52])).

fof(f233,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0)
      | r2_hidden(k4_tarski(sK7(X0,k4_relat_1(k6_relat_1(X1))),sK6(X0,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f172,f136])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X1))),sK7(X0,k4_relat_1(k6_relat_1(X1)))),k4_relat_1(k6_relat_1(X1)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X1))
      | r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X1))),X0) ) ),
    inference(resolution,[],[f139,f52])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK6(X2,k4_relat_1(X3)),sK7(X2,k4_relat_1(X3))),k4_relat_1(X3))
      | k6_relat_1(X2) = k4_relat_1(X3)
      | r2_hidden(sK6(X2,k4_relat_1(X3)),X2) ) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3104,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK6(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f3102])).

fof(f3102,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK6(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f3100,f256])).

fof(f3100,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f3098,f52])).

fof(f3098,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f1590,f54])).

fof(f1590,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f1589,f256])).

fof(f1589,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | sK6(X0,k4_relat_1(k6_relat_1(X0))) != sK7(X0,k4_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f1588,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | sK6(X0,X1) != sK7(X0,X1)
      | k6_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1588,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X0))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | sK6(X0,k4_relat_1(k6_relat_1(X0))) != sK7(X0,k4_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f1576])).

fof(f1576,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k4_relat_1(k6_relat_1(X0))),X0)
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | sK6(X0,k4_relat_1(k6_relat_1(X0))) != sK7(X0,k4_relat_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(k4_tarski(sK6(X0,k4_relat_1(k6_relat_1(X0))),sK7(X0,k4_relat_1(k6_relat_1(X0)))),k4_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(X0))) ) ),
    inference(resolution,[],[f840,f70])).

fof(f112,plain,
    ( k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_7
  <=> k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f113,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).

fof(f33,plain,
    ( ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',t72_relat_1)).
%------------------------------------------------------------------------------
