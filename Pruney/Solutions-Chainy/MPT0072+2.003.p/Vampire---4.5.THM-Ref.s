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
% DateTime   : Thu Dec  3 12:30:32 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  60 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f35,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f25,plain,(
    r2_hidden(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f17,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
   => ~ r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:42:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (811794433)
% 0.22/0.38  ipcrm: permission denied for id (811827202)
% 0.22/0.38  ipcrm: permission denied for id (815759363)
% 0.22/0.38  ipcrm: permission denied for id (811892740)
% 0.22/0.38  ipcrm: permission denied for id (811925509)
% 0.22/0.38  ipcrm: permission denied for id (811958278)
% 0.22/0.38  ipcrm: permission denied for id (811991047)
% 0.22/0.39  ipcrm: permission denied for id (815824905)
% 0.22/0.39  ipcrm: permission denied for id (812089354)
% 0.22/0.39  ipcrm: permission denied for id (812122123)
% 0.22/0.40  ipcrm: permission denied for id (815988751)
% 0.22/0.40  ipcrm: permission denied for id (812285968)
% 0.22/0.40  ipcrm: permission denied for id (812351506)
% 0.22/0.40  ipcrm: permission denied for id (812384275)
% 0.22/0.40  ipcrm: permission denied for id (812417044)
% 0.22/0.41  ipcrm: permission denied for id (812449813)
% 0.22/0.41  ipcrm: permission denied for id (812482582)
% 0.22/0.41  ipcrm: permission denied for id (812515351)
% 0.22/0.41  ipcrm: permission denied for id (812580889)
% 0.22/0.41  ipcrm: permission denied for id (812613658)
% 0.22/0.41  ipcrm: permission denied for id (812646427)
% 0.22/0.42  ipcrm: permission denied for id (812679196)
% 0.22/0.42  ipcrm: permission denied for id (812711965)
% 0.22/0.42  ipcrm: permission denied for id (812744735)
% 0.22/0.42  ipcrm: permission denied for id (812777504)
% 0.22/0.42  ipcrm: permission denied for id (812810273)
% 0.22/0.42  ipcrm: permission denied for id (812843042)
% 0.22/0.43  ipcrm: permission denied for id (812908581)
% 0.22/0.43  ipcrm: permission denied for id (812941350)
% 0.22/0.43  ipcrm: permission denied for id (816218151)
% 0.22/0.43  ipcrm: permission denied for id (812974120)
% 0.22/0.43  ipcrm: permission denied for id (813006889)
% 0.22/0.43  ipcrm: permission denied for id (816316460)
% 0.22/0.43  ipcrm: permission denied for id (816349229)
% 0.22/0.44  ipcrm: permission denied for id (816381998)
% 0.22/0.44  ipcrm: permission denied for id (813236271)
% 0.22/0.44  ipcrm: permission denied for id (813301809)
% 0.22/0.44  ipcrm: permission denied for id (816447538)
% 0.22/0.44  ipcrm: permission denied for id (813367347)
% 0.22/0.44  ipcrm: permission denied for id (813432885)
% 0.22/0.44  ipcrm: permission denied for id (813498423)
% 0.22/0.44  ipcrm: permission denied for id (813531192)
% 0.22/0.45  ipcrm: permission denied for id (813563961)
% 0.22/0.45  ipcrm: permission denied for id (816644157)
% 0.22/0.45  ipcrm: permission denied for id (813727806)
% 0.22/0.45  ipcrm: permission denied for id (816676927)
% 0.22/0.45  ipcrm: permission denied for id (816742465)
% 0.22/0.45  ipcrm: permission denied for id (813858882)
% 0.22/0.45  ipcrm: permission denied for id (813891651)
% 0.22/0.46  ipcrm: permission denied for id (814055496)
% 0.22/0.46  ipcrm: permission denied for id (814153804)
% 0.22/0.47  ipcrm: permission denied for id (814252112)
% 0.22/0.47  ipcrm: permission denied for id (814284881)
% 0.22/0.47  ipcrm: permission denied for id (814317650)
% 0.22/0.47  ipcrm: permission denied for id (817102931)
% 0.22/0.47  ipcrm: permission denied for id (814383188)
% 0.22/0.47  ipcrm: permission denied for id (814415957)
% 0.22/0.47  ipcrm: permission denied for id (814547032)
% 0.22/0.47  ipcrm: permission denied for id (814579802)
% 0.22/0.48  ipcrm: permission denied for id (814612571)
% 0.22/0.48  ipcrm: permission denied for id (817299549)
% 0.22/0.48  ipcrm: permission denied for id (817332318)
% 0.22/0.48  ipcrm: permission denied for id (814743647)
% 0.22/0.48  ipcrm: permission denied for id (817365088)
% 0.22/0.48  ipcrm: permission denied for id (817397857)
% 0.22/0.48  ipcrm: permission denied for id (817496162)
% 0.22/0.49  ipcrm: permission denied for id (814940261)
% 0.22/0.49  ipcrm: permission denied for id (817594471)
% 0.22/0.49  ipcrm: permission denied for id (817627240)
% 0.22/0.49  ipcrm: permission denied for id (817692778)
% 0.22/0.49  ipcrm: permission denied for id (815136875)
% 0.22/0.49  ipcrm: permission denied for id (815169644)
% 0.22/0.49  ipcrm: permission denied for id (815202413)
% 0.22/0.49  ipcrm: permission denied for id (815235182)
% 0.22/0.49  ipcrm: permission denied for id (815300720)
% 0.22/0.50  ipcrm: permission denied for id (815333489)
% 0.22/0.50  ipcrm: permission denied for id (817823860)
% 0.22/0.50  ipcrm: permission denied for id (817856629)
% 0.22/0.50  ipcrm: permission denied for id (817889398)
% 0.22/0.50  ipcrm: permission denied for id (815497335)
% 0.22/0.50  ipcrm: permission denied for id (815530104)
% 0.22/0.50  ipcrm: permission denied for id (815595642)
% 0.22/0.51  ipcrm: permission denied for id (818053246)
% 0.22/0.51  ipcrm: permission denied for id (818086015)
% 0.48/0.57  % (17474)WARNING: option uwaf not known.
% 0.48/0.57  % (17475)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.48/0.57  % (17474)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.48/0.57  % (17475)Refutation found. Thanks to Tanya!
% 0.48/0.57  % SZS status Theorem for theBenchmark
% 0.48/0.57  % SZS output start Proof for theBenchmark
% 0.48/0.57  fof(f36,plain,(
% 0.48/0.57    $false),
% 0.48/0.57    inference(subsumption_resolution,[],[f35,f18])).
% 0.48/0.57  fof(f18,plain,(
% 0.48/0.57    v1_xboole_0(k1_xboole_0)),
% 0.48/0.57    inference(cnf_transformation,[],[f2])).
% 0.48/0.57  fof(f2,axiom,(
% 0.48/0.57    v1_xboole_0(k1_xboole_0)),
% 0.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.48/0.57  fof(f35,plain,(
% 0.48/0.57    ~v1_xboole_0(k1_xboole_0)),
% 0.48/0.57    inference(resolution,[],[f25,f19])).
% 0.48/0.57  fof(f19,plain,(
% 0.48/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.48/0.57    inference(cnf_transformation,[],[f14])).
% 0.48/0.57  fof(f14,plain,(
% 0.48/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).
% 0.48/0.57  fof(f13,plain,(
% 0.48/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.48/0.57    introduced(choice_axiom,[])).
% 0.48/0.57  fof(f12,plain,(
% 0.48/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.48/0.57    inference(rectify,[],[f11])).
% 0.48/0.57  fof(f11,plain,(
% 0.48/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.48/0.57    inference(nnf_transformation,[],[f1])).
% 0.48/0.57  fof(f1,axiom,(
% 0.48/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.48/0.57  fof(f25,plain,(
% 0.48/0.57    r2_hidden(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.48/0.57    inference(resolution,[],[f17,f22])).
% 0.48/0.57  fof(f22,plain,(
% 0.48/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.48/0.57    inference(cnf_transformation,[],[f16])).
% 0.48/0.57  fof(f16,plain,(
% 0.48/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f15])).
% 0.48/0.57  fof(f15,plain,(
% 0.48/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.48/0.57    introduced(choice_axiom,[])).
% 0.48/0.57  fof(f8,plain,(
% 0.48/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.48/0.57    inference(ennf_transformation,[],[f6])).
% 0.48/0.57  fof(f6,plain,(
% 0.48/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.48/0.57    inference(rectify,[],[f3])).
% 0.48/0.57  fof(f3,axiom,(
% 0.48/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.48/0.57  fof(f17,plain,(
% 0.48/0.57    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.48/0.57    inference(cnf_transformation,[],[f10])).
% 0.48/0.57  fof(f10,plain,(
% 0.48/0.57    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).
% 0.48/0.57  fof(f9,plain,(
% 0.48/0.57    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0) => ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.48/0.57    introduced(choice_axiom,[])).
% 0.48/0.57  fof(f7,plain,(
% 0.48/0.57    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.48/0.57    inference(ennf_transformation,[],[f5])).
% 0.48/0.57  fof(f5,negated_conjecture,(
% 0.48/0.57    ~! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.48/0.57    inference(negated_conjecture,[],[f4])).
% 0.48/0.57  fof(f4,conjecture,(
% 0.48/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.48/0.57  % SZS output end Proof for theBenchmark
% 0.48/0.57  % (17475)------------------------------
% 0.48/0.57  % (17475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.48/0.57  % (17475)Termination reason: Refutation
% 0.48/0.57  
% 0.48/0.57  % (17475)Memory used [KB]: 5373
% 0.48/0.57  % (17475)Time elapsed: 0.031 s
% 0.48/0.57  % (17475)------------------------------
% 0.48/0.57  % (17475)------------------------------
% 0.48/0.57  % (17477)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.48/0.57  % (17476)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.48/0.57  % (17326)Success in time 0.211 s
%------------------------------------------------------------------------------
