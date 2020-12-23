%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 106 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 ( 578 expanded)
%              Number of equality atoms :   17 (  37 expanded)
%              Maximal formula depth    :   14 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(subsumption_resolution,[],[f519,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(f519,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f506,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f506,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f370,f27])).

fof(f27,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f370,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f197,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X3),X2)
      | r1_tarski(k7_relat_1(X0,X1),X3)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X3),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r1_tarski(k7_relat_1(X0,X1),X3)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

% (16008)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f197,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4)
      | ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) ) ),
    inference(subsumption_resolution,[],[f195,f37])).

fof(f195,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4)
      | ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))
      | ~ v1_relat_1(k7_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4)
      | ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))
      | ~ v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) ) ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(X8,k7_relat_1(X9,X10)),sK4(X8,k7_relat_1(X9,X10))),X9)
      | ~ r2_hidden(sK3(X8,k7_relat_1(X9,X10)),X10)
      | ~ v1_relat_1(X9)
      | r1_tarski(X8,k7_relat_1(X9,X10))
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f64,f37])).

fof(f64,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(X8,k7_relat_1(X9,X10)),sK4(X8,k7_relat_1(X9,X10))),X9)
      | ~ r2_hidden(sK3(X8,k7_relat_1(X9,X10)),X10)
      | ~ v1_relat_1(k7_relat_1(X9,X10))
      | ~ v1_relat_1(X9)
      | r1_tarski(X8,k7_relat_1(X9,X10))
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (16010)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.42  % (16018)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (16010)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % (16014)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f520,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f519,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).
% 0.21/0.46  fof(f519,plain,(
% 0.21/0.46    ~r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f506,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f506,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(resolution,[],[f370,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f370,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) | ~v1_relat_1(X2) | ~r1_tarski(X3,X4)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f363])).
% 0.21/0.46  fof(f363,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) | ~r1_tarski(X3,X4) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(resolution,[],[f197,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(k7_relat_1(X0,X1),X3),X2) | r1_tarski(k7_relat_1(X0,X1),X3) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f55,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(k7_relat_1(X0,X1),X3),X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | r1_tarski(k7_relat_1(X0,X1),X3) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(superposition,[],[f53,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f37])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK3(k7_relat_1(X0,X1),X2),X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2) | ~v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.46    inference(resolution,[],[f41,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f21])).
% 0.21/0.46  % (16008)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f195,f37])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) | ~v1_relat_1(k7_relat_1(X2,X3))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~r2_hidden(sK3(k7_relat_1(X2,X3),k7_relat_1(X2,X4)),X4) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(X2,X4))) )),
% 0.21/0.46    inference(resolution,[],[f71,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f60,f37])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(k7_relat_1(X0,X1),X2),sK4(k7_relat_1(X0,X1),X2)),X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),X2) | ~v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.46    inference(resolution,[],[f40,f29])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(k4_tarski(X5,X6),X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(sK3(X8,k7_relat_1(X9,X10)),sK4(X8,k7_relat_1(X9,X10))),X9) | ~r2_hidden(sK3(X8,k7_relat_1(X9,X10)),X10) | ~v1_relat_1(X9) | r1_tarski(X8,k7_relat_1(X9,X10)) | ~v1_relat_1(X8)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f64,f37])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(sK3(X8,k7_relat_1(X9,X10)),sK4(X8,k7_relat_1(X9,X10))),X9) | ~r2_hidden(sK3(X8,k7_relat_1(X9,X10)),X10) | ~v1_relat_1(k7_relat_1(X9,X10)) | ~v1_relat_1(X9) | r1_tarski(X8,k7_relat_1(X9,X10)) | ~v1_relat_1(X8)) )),
% 0.21/0.46    inference(resolution,[],[f39,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (16010)------------------------------
% 0.21/0.46  % (16010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16010)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (16010)Memory used [KB]: 11001
% 0.21/0.46  % (16010)Time elapsed: 0.062 s
% 0.21/0.46  % (16010)------------------------------
% 0.21/0.46  % (16010)------------------------------
% 0.21/0.47  % (16006)Success in time 0.11 s
%------------------------------------------------------------------------------
