%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 147 expanded)
%              Number of leaves         :    5 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  105 ( 475 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(subsumption_resolution,[],[f264,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f264,plain,(
    k1_xboole_0 = sK0 ),
    inference(superposition,[],[f228,f13])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f228,plain,(
    ! [X6] : sK0 = k4_xboole_0(X6,X6) ),
    inference(resolution,[],[f223,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | sK0 = k4_xboole_0(X0,X0) ) ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK0)
      | r2_hidden(sK1(sK2(sK0),sK0),sK0) ) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f29,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK1(X1,sK0),sK0) ) ),
    inference(resolution,[],[f11,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f11,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | sK0 = k4_xboole_0(X0,X0)
      | r2_hidden(sK3(X0,X0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | sK0 = k4_xboole_0(X0,X0)
      | r2_hidden(sK3(X0,X0,sK0),sK0)
      | sK0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f53,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK3(X7,X8,sK0),X7)
      | r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | sK0 = k4_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f43,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f223,plain,(
    ! [X4] : ~ r2_hidden(X4,sK0) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f26,f212])).

fof(f212,plain,(
    sK0 = k4_xboole_0(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( sK0 != sK0
    | sK0 = k4_xboole_0(sK0,sK0) ),
    inference(equality_factoring,[],[f177])).

fof(f177,plain,(
    ! [X10,X11] :
      ( sK0 = k4_xboole_0(sK0,X10)
      | sK0 = k4_xboole_0(X11,X11) ) ),
    inference(resolution,[],[f172,f87])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f164,plain,(
    ! [X0,X1] :
      ( sK0 = k4_xboole_0(sK0,X0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK1(sK2(sK0),sK0),sK0) ) ),
    inference(resolution,[],[f88,f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,sK2(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X30] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
      | sK0 = k4_xboole_0(sK0,X30) ) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f34,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK0)
      | r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ) ),
    inference(resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK1(X0,sK0),X0) ) ),
    inference(resolution,[],[f11,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X30] :
      ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
      | sK0 = k4_xboole_0(sK0,X30)
      | r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ) ),
    inference(resolution,[],[f53,f34])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (6803)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (6812)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (6813)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (6804)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (6805)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (6811)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (6811)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (6813)Refutation not found, incomplete strategy% (6813)------------------------------
% 0.22/0.51  % (6813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6813)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6813)Memory used [KB]: 6140
% 0.22/0.51  % (6813)Time elapsed: 0.081 s
% 0.22/0.51  % (6813)------------------------------
% 0.22/0.51  % (6813)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f264,f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(superposition,[],[f228,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ( ! [X6] : (sK0 = k4_xboole_0(X6,X6)) )),
% 0.22/0.51    inference(resolution,[],[f223,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK1(sK2(sK0),sK0),sK0) | sK0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f86,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK1(sK2(sK0),sK0),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f29,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(sK1(X1,sK0),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f11,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK1(sK2(sK0),sK0),sK0) | sK0 = k4_xboole_0(X0,X0) | r2_hidden(sK3(X0,X0,sK0),sK0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK1(sK2(sK0),sK0),sK0) | sK0 = k4_xboole_0(X0,X0) | r2_hidden(sK3(X0,X0,sK0),sK0) | sK0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f53,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X8,X7] : (r2_hidden(sK3(X7,X8,sK0),X7) | r2_hidden(sK1(sK2(sK0),sK0),sK0) | sK0 = k4_xboole_0(X7,X8)) )),
% 0.22/0.51    inference(resolution,[],[f43,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,sK0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f220])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,sK0) | ~r2_hidden(X4,sK0)) )),
% 0.22/0.51    inference(superposition,[],[f26,f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    sK0 != sK0 | sK0 = k4_xboole_0(sK0,sK0)),
% 0.22/0.51    inference(equality_factoring,[],[f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X10,X11] : (sK0 = k4_xboole_0(sK0,X10) | sK0 = k4_xboole_0(X11,X11)) )),
% 0.22/0.51    inference(resolution,[],[f172,f87])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f43])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK0 = k4_xboole_0(sK0,X0) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK1(sK2(sK0),sK0),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f88,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,sK2(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X30] : (r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | sK0 = k4_xboole_0(sK0,X30)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f28,f18])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(X0,sK0),X0)) )),
% 0.22/0.51    inference(resolution,[],[f11,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X30] : (r2_hidden(sK1(sK2(sK0),sK0),sK0) | sK0 = k4_xboole_0(sK0,X30) | r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f53,f34])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (6811)------------------------------
% 0.22/0.51  % (6811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6811)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (6811)Memory used [KB]: 1663
% 0.22/0.51  % (6811)Time elapsed: 0.082 s
% 0.22/0.51  % (6811)------------------------------
% 0.22/0.51  % (6811)------------------------------
% 0.22/0.51  % (6797)Success in time 0.151 s
%------------------------------------------------------------------------------
