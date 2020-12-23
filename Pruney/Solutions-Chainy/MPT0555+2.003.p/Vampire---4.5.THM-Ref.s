%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 136 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 ( 679 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(subsumption_resolution,[],[f285,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f285,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f265,f31])).

fof(f31,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

% (9966)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f265,plain,
    ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f243,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),X0)
      | ~ r1_tarski(X0,k9_relat_1(sK2,sK0)) ) ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK6(X0,X1),X2) ) ),
    inference(resolution,[],[f38,f40])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f243,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK6(k9_relat_1(sK1,X11),X12),k9_relat_1(sK2,X11))
      | r1_tarski(k9_relat_1(sK1,X11),X12) ) ),
    inference(resolution,[],[f238,f39])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f237,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f237,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k9_relat_1(sK2,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k9_relat_1(sK2,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f221,f46])).

fof(f46,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

% (9974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f221,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK5(sK1,X4,X3),X5)
      | r2_hidden(X3,k9_relat_1(sK2,X5))
      | ~ r2_hidden(X3,k9_relat_1(sK1,X4)) ) ),
    inference(subsumption_resolution,[],[f220,f30])).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f220,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK1,X4))
      | r2_hidden(X3,k9_relat_1(sK2,X5))
      | ~ r2_hidden(sK5(sK1,X4,X3),X5)
      | ~ r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f217,f150])).

fof(f150,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X5),X6)
      | r2_hidden(X5,k9_relat_1(sK2,X4))
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X6,sK2) ) ),
    inference(resolution,[],[f145,f38])).

fof(f145,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X5),sK2)
      | ~ r2_hidden(X3,X4)
      | r2_hidden(X5,k9_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | r2_hidden(X6,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f217,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (9955)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (9970)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (9964)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9980)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (9972)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.56  % (9955)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f286,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(subsumption_resolution,[],[f285,f50])).
% 1.57/0.56  fof(f50,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.57/0.56    inference(duplicate_literal_removal,[],[f49])).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.57/0.56    inference(resolution,[],[f40,f39])).
% 1.57/0.56  fof(f39,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f23,plain,(
% 1.57/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).
% 1.57/0.56  fof(f22,plain,(
% 1.57/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f21,plain,(
% 1.57/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.56    inference(rectify,[],[f20])).
% 1.57/0.56  fof(f20,plain,(
% 1.57/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.56    inference(nnf_transformation,[],[f9])).
% 1.57/0.56  fof(f9,plain,(
% 1.57/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.56  fof(f40,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f285,plain,(
% 1.57/0.56    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 1.57/0.56    inference(subsumption_resolution,[],[f265,f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f13,plain,(
% 1.57/0.56    (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 1.57/0.56  fof(f11,plain,(
% 1.57/0.56    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f12,plain,(
% 1.57/0.56    ? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f7,plain,(
% 1.57/0.56    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 1.57/0.56    inference(flattening,[],[f6])).
% 1.57/0.56  fof(f6,plain,(
% 1.57/0.56    ? [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f5])).
% 1.57/0.56  fof(f5,negated_conjecture,(
% 1.57/0.56    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 1.57/0.56    inference(negated_conjecture,[],[f4])).
% 1.57/0.56  % (9966)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.56  fof(f4,conjecture,(
% 1.57/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 1.57/0.56  fof(f265,plain,(
% 1.57/0.56    r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 1.57/0.56    inference(resolution,[],[f243,f52])).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    ( ! [X0] : (~r2_hidden(sK6(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),X0) | ~r1_tarski(X0,k9_relat_1(sK2,sK0))) )),
% 1.57/0.56    inference(resolution,[],[f51,f31])).
% 1.57/0.56  fof(f51,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK6(X0,X1),X2)) )),
% 1.57/0.56    inference(resolution,[],[f38,f40])).
% 1.57/0.56  fof(f38,plain,(
% 1.57/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f243,plain,(
% 1.57/0.56    ( ! [X12,X11] : (r2_hidden(sK6(k9_relat_1(sK1,X11),X12),k9_relat_1(sK2,X11)) | r1_tarski(k9_relat_1(sK1,X11),X12)) )),
% 1.57/0.56    inference(resolution,[],[f238,f39])).
% 1.57/0.56  fof(f238,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f237,f28])).
% 1.57/0.56  fof(f28,plain,(
% 1.57/0.56    v1_relat_1(sK1)),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f237,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(X0,k9_relat_1(sK2,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.57/0.56    inference(duplicate_literal_removal,[],[f235])).
% 1.57/0.56  fof(f235,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(X0,k9_relat_1(sK2,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.57/0.56    inference(resolution,[],[f221,f46])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ( ! [X6,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f19])).
% 1.57/0.56  fof(f19,plain,(
% 1.57/0.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 1.57/0.56  fof(f16,plain,(
% 1.57/0.56    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f17,plain,(
% 1.57/0.56    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f18,plain,(
% 1.57/0.56    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f15,plain,(
% 1.57/0.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(rectify,[],[f14])).
% 1.57/0.56  % (9974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.56  fof(f14,plain,(
% 1.57/0.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(nnf_transformation,[],[f8])).
% 1.57/0.56  fof(f8,plain,(
% 1.57/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 1.57/0.56  fof(f221,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (~r2_hidden(sK5(sK1,X4,X3),X5) | r2_hidden(X3,k9_relat_1(sK2,X5)) | ~r2_hidden(X3,k9_relat_1(sK1,X4))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f220,f30])).
% 1.57/0.56  fof(f30,plain,(
% 1.57/0.56    r1_tarski(sK1,sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f220,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (~r2_hidden(X3,k9_relat_1(sK1,X4)) | r2_hidden(X3,k9_relat_1(sK2,X5)) | ~r2_hidden(sK5(sK1,X4,X3),X5) | ~r1_tarski(sK1,sK2)) )),
% 1.57/0.56    inference(resolution,[],[f217,f150])).
% 1.57/0.56  fof(f150,plain,(
% 1.57/0.56    ( ! [X6,X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X5),X6) | r2_hidden(X5,k9_relat_1(sK2,X4)) | ~r2_hidden(X3,X4) | ~r1_tarski(X6,sK2)) )),
% 1.57/0.56    inference(resolution,[],[f145,f38])).
% 1.57/0.56  fof(f145,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X5),sK2) | ~r2_hidden(X3,X4) | r2_hidden(X5,k9_relat_1(sK2,X4))) )),
% 1.57/0.56    inference(resolution,[],[f45,f29])).
% 1.57/0.56  fof(f29,plain,(
% 1.57/0.56    v1_relat_1(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f45,plain,(
% 1.57/0.56    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | r2_hidden(X6,k9_relat_1(X0,X1))) )),
% 1.57/0.56    inference(equality_resolution,[],[f34])).
% 1.57/0.56  fof(f34,plain,(
% 1.57/0.56    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f19])).
% 1.57/0.56  fof(f217,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK1,X1,X0),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.57/0.56    inference(resolution,[],[f47,f28])).
% 1.57/0.56  fof(f47,plain,(
% 1.57/0.56    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f32])).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f19])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (9955)------------------------------
% 1.57/0.56  % (9955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (9955)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (9955)Memory used [KB]: 11001
% 1.57/0.56  % (9955)Time elapsed: 0.136 s
% 1.57/0.56  % (9955)------------------------------
% 1.57/0.56  % (9955)------------------------------
% 1.57/0.57  % (9951)Success in time 0.206 s
%------------------------------------------------------------------------------
