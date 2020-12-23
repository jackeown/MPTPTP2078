%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 154 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 583 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f28,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

% (7990)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (7991)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f15,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f64,plain,(
    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f57])).

fof(f57,plain,(
    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f55,f55,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f62,f52])).

fof(f62,plain,(
    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f61,f50])).

fof(f50,plain,(
    ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (7981)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (7989)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (7976)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (7989)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f53,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f28,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 0.21/0.47  % (7990)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  % (7991)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f28,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0)),
% 0.21/0.47    inference(forward_demodulation,[],[f63,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f26,f55,f55,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_xboole_0))),
% 0.21/0.47    inference(forward_demodulation,[],[f62,f52])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.47    inference(forward_demodulation,[],[f61,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f26,f27,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    r2_hidden(sK6(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f29,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7989)------------------------------
% 0.21/0.47  % (7989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7989)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7989)Memory used [KB]: 6140
% 0.21/0.47  % (7989)Time elapsed: 0.068 s
% 0.21/0.47  % (7989)------------------------------
% 0.21/0.47  % (7989)------------------------------
% 0.21/0.48  % (7973)Success in time 0.121 s
%------------------------------------------------------------------------------
