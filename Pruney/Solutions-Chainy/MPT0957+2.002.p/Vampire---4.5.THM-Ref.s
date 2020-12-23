%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  71 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   17
%              Number of atoms          :  180 ( 362 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f48,plain,(
    ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f22,plain,(
    ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
    ( ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0)
   => ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord2)).

fof(f47,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK6(X0,X1),X1)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(f45,plain,(
    ~ r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f44,f24])).

fof(f44,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f43,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ) ),
    inference(resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X4,X2,X3] :
      ( r8_relat_2(k1_wellord2(X2),X3)
      | ~ r2_hidden(k4_tarski(X4,sK6(k1_wellord2(X2),X3)),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),X4),k1_wellord2(X2)) ) ),
    inference(subsumption_resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),X4),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X4,sK6(k1_wellord2(X2),X3)),k1_wellord2(X2))
      | r8_relat_2(k1_wellord2(X2),X3)
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    inference(subsumption_resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),k1_wellord2(X2))
      | r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2))
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(f25,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v8_relat_2(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15538)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.46  % (15538)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f48,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f47,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : ~r8_relat_2(k1_wellord2(X0),X0) => ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : ~r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord2)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(resolution,[],[f45,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f44,f24])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ~r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f43,f22])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ~r2_hidden(k4_tarski(sK5(k1_wellord2(sK0),sK0),sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(resolution,[],[f41,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) | ~r2_hidden(k4_tarski(X0,sK6(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f40,f22])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (r8_relat_2(k1_wellord2(X2),X3) | ~r2_hidden(k4_tarski(X4,sK6(k1_wellord2(X2),X3)),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),X4),k1_wellord2(X2))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f39,f24])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),X4),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X4,sK6(k1_wellord2(X2),X3)),k1_wellord2(X2)) | r8_relat_2(k1_wellord2(X2),X3) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.21/0.46    inference(resolution,[],[f37,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X3,X0),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f36,f24])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X3,X0),k1_wellord2(X2)) | r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.21/0.46    inference(resolution,[],[f25,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0] : (v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X6,X4,X0,X5] : (~v8_relat_2(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X6),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (15538)------------------------------
% 0.21/0.46  % (15538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15538)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (15538)Memory used [KB]: 5373
% 0.21/0.46  % (15538)Time elapsed: 0.054 s
% 0.21/0.46  % (15538)------------------------------
% 0.21/0.46  % (15538)------------------------------
% 0.21/0.47  % (15537)Success in time 0.111 s
%------------------------------------------------------------------------------
