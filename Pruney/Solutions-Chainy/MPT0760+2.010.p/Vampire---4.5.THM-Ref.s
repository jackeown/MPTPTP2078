%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  48 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 200 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f49,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f49,plain,(
    r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f20,f22,f47,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_wellord1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f20,f21,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f21,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k1_wellord1(sK1,sK0)
    & ~ r2_hidden(sK0,k3_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK1,sK0)
      & ~ r2_hidden(sK0,k3_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(f22,plain,(
    k1_xboole_0 != k1_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (4669)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.41  % (4669)Refutation not found, incomplete strategy% (4669)------------------------------
% 0.19/0.41  % (4669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (4669)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.41  
% 0.19/0.41  % (4669)Memory used [KB]: 1535
% 0.19/0.41  % (4669)Time elapsed: 0.003 s
% 0.19/0.41  % (4669)------------------------------
% 0.19/0.41  % (4669)------------------------------
% 0.20/0.46  % (4671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (4671)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f23,f49,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f20,f22,f47,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k1_wellord1(X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK1)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f20,f21,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k3_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    k1_xboole_0 != k1_wellord1(sK1,sK0) & ~r2_hidden(sK0,k3_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK1,sK0) & ~r2_hidden(sK0,k3_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k1_xboole_0 != k1_wellord1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4671)------------------------------
% 0.20/0.47  % (4671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4671)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4671)Memory used [KB]: 6140
% 0.20/0.47  % (4671)Time elapsed: 0.061 s
% 0.20/0.47  % (4671)------------------------------
% 0.20/0.47  % (4671)------------------------------
% 0.20/0.47  % (4655)Success in time 0.119 s
%------------------------------------------------------------------------------
