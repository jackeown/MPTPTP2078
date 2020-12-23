%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t140_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 44.34s
% Output     : Refutation 44.34s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 523 expanded)
%              Number of leaves         :   14 ( 140 expanded)
%              Depth                    :   21
%              Number of atoms          :  482 (2237 expanded)
%              Number of equality atoms :   39 ( 354 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2440,f2737,f2792,f2904,f2973,f3100])).

fof(f3100,plain,
    ( spl9_9
    | spl9_71 ),
    inference(avatar_contradiction_clause,[],[f3099])).

fof(f3099,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3098,f79])).

fof(f79,plain,(
    ! [X12] : v1_relat_1(k8_relat_1(X12,sK2)) ),
    inference(resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t140_relat_1.p',dt_k8_relat_1)).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k7_relat_1(k8_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k7_relat_1(X2,X1)) != k7_relat_1(k8_relat_1(X0,X2),X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k7_relat_1(k8_relat_1(sK0,sK2),sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k7_relat_1(X2,X1)) != k7_relat_1(k8_relat_1(X0,X2),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k7_relat_1(X2,X1)) = k7_relat_1(k8_relat_1(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k7_relat_1(X2,X1)) = k7_relat_1(k8_relat_1(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t140_relat_1.p',t140_relat_1)).

fof(f3098,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3097,f160])).

fof(f160,plain,(
    ! [X28,X27] : v1_relat_1(k8_relat_1(X27,k7_relat_1(sK2,X28))) ),
    inference(resolution,[],[f80,f50])).

fof(f80,plain,(
    ! [X13] : v1_relat_1(k7_relat_1(sK2,X13)) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t140_relat_1.p',dt_k7_relat_1)).

fof(f3097,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3096,f3095])).

fof(f3095,plain,
    ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3094,f42])).

fof(f3094,plain,
    ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3074,f80])).

fof(f3074,plain,
    ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_9
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f3054,f2975])).

fof(f2975,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2974,f42])).

fof(f2974,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2950,f79])).

fof(f2950,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_9 ),
    inference(resolution,[],[f2889,f64])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK4(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
                    & r2_hidden(sK4(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t140_relat_1.p',d12_relat_1)).

fof(f2889,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2888,f79])).

fof(f2888,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2887,f160])).

fof(f2887,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2866,f43])).

fof(f43,plain,(
    k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k7_relat_1(k8_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f2866,plain,
    ( k8_relat_1(sK0,k7_relat_1(sK2,sK1)) = k7_relat_1(k8_relat_1(sK0,sK2),sK1)
    | r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(resolution,[],[f2181,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK5(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                    & r2_hidden(sK5(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t140_relat_1.p',d11_relat_1)).

fof(f2181,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f2180])).

fof(f2180,plain,
    ( spl9_9
  <=> ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f3054,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_71 ),
    inference(resolution,[],[f2903,f66])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2903,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f2902])).

fof(f2902,plain,
    ( spl9_71
  <=> ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f3096,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2865,f43])).

fof(f2865,plain,
    ( k8_relat_1(sK0,k7_relat_1(sK2,sK1)) = k7_relat_1(k8_relat_1(sK0,sK2),sK1)
    | r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_9 ),
    inference(resolution,[],[f2181,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2973,plain,
    ( spl9_9
    | spl9_69 ),
    inference(avatar_contradiction_clause,[],[f2972])).

fof(f2972,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_69 ),
    inference(subsumption_resolution,[],[f2971,f42])).

fof(f2971,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_9
    | ~ spl9_69 ),
    inference(subsumption_resolution,[],[f2970,f79])).

fof(f2970,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_9
    | ~ spl9_69 ),
    inference(subsumption_resolution,[],[f2949,f2897])).

fof(f2897,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f2896,plain,
    ( spl9_69
  <=> ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f2949,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_9 ),
    inference(resolution,[],[f2889,f65])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2904,plain,
    ( ~ spl9_69
    | ~ spl9_71
    | spl9_9 ),
    inference(avatar_split_clause,[],[f2891,f2180,f2902,f2896])).

fof(f2891,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2890,f80])).

fof(f2890,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f2867,f160])).

fof(f2867,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_9 ),
    inference(resolution,[],[f2181,f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2792,plain,
    ( ~ spl9_8
    | spl9_67 ),
    inference(avatar_contradiction_clause,[],[f2791])).

fof(f2791,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f2790,f42])).

fof(f2790,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f2789,f79])).

fof(f2789,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f2788,f2442])).

fof(f2442,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2441,f80])).

fof(f2441,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2410,f160])).

fof(f2410,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_8 ),
    inference(resolution,[],[f2184,f65])).

fof(f2184,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f2183])).

fof(f2183,plain,
    ( spl9_8
  <=> r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2788,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f2768,f2739])).

fof(f2739,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2738,f42])).

fof(f2738,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2714,f80])).

fof(f2714,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(resolution,[],[f2444,f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2444,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2443,f80])).

fof(f2443,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2411,f160])).

fof(f2411,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl9_8 ),
    inference(resolution,[],[f2184,f64])).

fof(f2768,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_67 ),
    inference(resolution,[],[f2439,f63])).

fof(f2439,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f2438])).

fof(f2438,plain,
    ( spl9_67
  <=> ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f2737,plain,
    ( ~ spl9_8
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f2736])).

fof(f2736,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f2735,f42])).

fof(f2735,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f2734,f80])).

fof(f2734,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f2713,f2187])).

fof(f2187,plain,
    ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f2186])).

fof(f2186,plain,
    ( spl9_11
  <=> ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f2713,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(resolution,[],[f2444,f68])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2440,plain,
    ( ~ spl9_11
    | ~ spl9_67
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f2433,f2183,f2438,f2186])).

fof(f2433,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2432,f79])).

fof(f2432,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2431,f160])).

fof(f2431,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f2409,f43])).

fof(f2409,plain,
    ( k8_relat_1(sK0,k7_relat_1(sK2,sK1)) = k7_relat_1(k8_relat_1(sK0,sK2),sK1)
    | ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK6(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1)))),k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),sK1,k8_relat_1(sK0,k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl9_8 ),
    inference(resolution,[],[f2184,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
