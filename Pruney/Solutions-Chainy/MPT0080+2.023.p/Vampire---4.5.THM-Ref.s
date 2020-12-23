%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:02 EST 2020

% Result     : Theorem 6.24s
% Output     : Refutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 190 expanded)
%              Number of leaves         :    5 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 589 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7450,plain,(
    $false ),
    inference(global_subsumption,[],[f7434,f7424])).

fof(f7424,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f7370,f1220])).

fof(f1220,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(k4_xboole_0(X3,X4),X5),X4)
      | r1_xboole_0(k4_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f182,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( sP6(sK3(k4_xboole_0(X0,X1),X2),X1,X0)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f7370,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f457,f160,f7342,f366])).

fof(f366,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X9,k2_xboole_0(X7,X8))
      | ~ r1_xboole_0(X6,X8)
      | ~ r1_xboole_0(X6,X7)
      | ~ r2_hidden(X9,X6) ) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f7342,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(duplicate_literal_removal,[],[f7323])).

fof(f7323,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,X0),sK2)
      | r1_xboole_0(k4_xboole_0(sK0,X0),sK2) ) ),
    inference(resolution,[],[f1221,f442])).

fof(f442,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK2),sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f128,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1221,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X6)
      | r1_xboole_0(k4_xboole_0(X6,X7),X8) ) ),
    inference(resolution,[],[f182,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f160,plain,(
    r2_hidden(sK4(sK0,sK1),k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f60,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    r2_hidden(sK4(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f457,plain,(
    r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f238,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f238,plain,(
    sP6(sK4(sK0,sK1),sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f60,f61,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ~ r2_hidden(sK4(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7434,plain,(
    r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f63,f7370,f165])).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4),X5)
      | ~ r1_tarski(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f30,f28])).

fof(f63,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:01:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.44  % (5103)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (5095)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (5111)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.49  % (5094)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (5106)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.49  % (5098)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (5102)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (5104)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (5099)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (5093)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (5116)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (5097)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5118)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (5100)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (5108)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (5114)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (5109)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (5105)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5119)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (5096)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (5115)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (5117)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (5107)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (5121)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (5122)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (5110)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (5113)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (5112)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (5120)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.55  % (5101)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 3.26/0.79  % (5098)Time limit reached!
% 3.26/0.79  % (5098)------------------------------
% 3.26/0.79  % (5098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.80  % (5098)Termination reason: Time limit
% 3.26/0.80  % (5098)Termination phase: Saturation
% 3.26/0.80  
% 3.26/0.80  % (5098)Memory used [KB]: 9978
% 3.26/0.80  % (5098)Time elapsed: 0.400 s
% 3.26/0.80  % (5098)------------------------------
% 3.26/0.80  % (5098)------------------------------
% 3.98/0.89  % (5105)Time limit reached!
% 3.98/0.89  % (5105)------------------------------
% 3.98/0.89  % (5105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.90  % (5105)Termination reason: Time limit
% 3.98/0.90  
% 3.98/0.90  % (5105)Memory used [KB]: 9210
% 3.98/0.90  % (5105)Time elapsed: 0.507 s
% 3.98/0.90  % (5105)------------------------------
% 3.98/0.90  % (5105)------------------------------
% 3.98/0.92  % (5093)Time limit reached!
% 3.98/0.92  % (5093)------------------------------
% 3.98/0.92  % (5093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (5123)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.98/0.92  % (5094)Time limit reached!
% 3.98/0.92  % (5094)------------------------------
% 3.98/0.92  % (5094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.92  % (5093)Termination reason: Time limit
% 3.98/0.92  
% 3.98/0.92  % (5093)Memory used [KB]: 4221
% 3.98/0.92  % (5093)Time elapsed: 0.530 s
% 3.98/0.92  % (5093)------------------------------
% 3.98/0.92  % (5093)------------------------------
% 4.47/0.93  % (5094)Termination reason: Time limit
% 4.47/0.93  
% 4.47/0.93  % (5094)Memory used [KB]: 9210
% 4.47/0.93  % (5094)Time elapsed: 0.527 s
% 4.47/0.93  % (5094)------------------------------
% 4.47/0.93  % (5094)------------------------------
% 4.47/0.93  % (5110)Time limit reached!
% 4.47/0.93  % (5110)------------------------------
% 4.47/0.93  % (5110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.93  % (5110)Termination reason: Time limit
% 4.47/0.93  % (5110)Termination phase: Saturation
% 4.47/0.93  
% 4.47/0.93  % (5110)Memory used [KB]: 15351
% 4.47/0.93  % (5110)Time elapsed: 0.522 s
% 4.47/0.93  % (5110)------------------------------
% 4.47/0.93  % (5110)------------------------------
% 4.47/0.94  % (5103)Time limit reached!
% 4.47/0.94  % (5103)------------------------------
% 4.47/0.94  % (5103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.95  % (5103)Termination reason: Time limit
% 4.47/0.95  % (5103)Termination phase: Saturation
% 4.47/0.95  
% 4.47/0.95  % (5103)Memory used [KB]: 12792
% 4.47/0.95  % (5103)Time elapsed: 0.500 s
% 4.47/0.95  % (5103)------------------------------
% 4.47/0.95  % (5103)------------------------------
% 4.77/0.98  % (5124)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.77/0.98  % (5121)Time limit reached!
% 4.77/0.98  % (5121)------------------------------
% 4.77/0.98  % (5121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.00  % (5121)Termination reason: Time limit
% 4.77/1.00  % (5121)Termination phase: Saturation
% 4.77/1.00  
% 4.77/1.00  % (5121)Memory used [KB]: 9210
% 4.77/1.00  % (5121)Time elapsed: 0.600 s
% 4.77/1.00  % (5121)------------------------------
% 4.77/1.00  % (5121)------------------------------
% 4.77/1.02  % (5109)Time limit reached!
% 4.77/1.02  % (5109)------------------------------
% 4.77/1.02  % (5109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.02  % (5109)Termination reason: Time limit
% 4.77/1.02  
% 4.77/1.02  % (5109)Memory used [KB]: 16247
% 4.77/1.02  % (5109)Time elapsed: 0.631 s
% 4.77/1.02  % (5109)------------------------------
% 4.77/1.02  % (5109)------------------------------
% 5.24/1.04  % (5100)Time limit reached!
% 5.24/1.04  % (5100)------------------------------
% 5.24/1.04  % (5100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.04  % (5100)Termination reason: Time limit
% 5.24/1.04  % (5100)Termination phase: Saturation
% 5.24/1.04  
% 5.24/1.04  % (5100)Memory used [KB]: 10746
% 5.24/1.04  % (5100)Time elapsed: 0.600 s
% 5.24/1.04  % (5100)------------------------------
% 5.24/1.04  % (5100)------------------------------
% 5.24/1.06  % (5127)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.24/1.06  % (5125)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.24/1.06  % (5126)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.71/1.09  % (5128)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.71/1.10  % (5129)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.71/1.14  % (5131)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.24/1.15  % (5117)Refutation found. Thanks to Tanya!
% 6.24/1.15  % SZS status Theorem for theBenchmark
% 6.24/1.15  % SZS output start Proof for theBenchmark
% 6.24/1.15  fof(f7450,plain,(
% 6.24/1.15    $false),
% 6.24/1.15    inference(global_subsumption,[],[f7434,f7424])).
% 6.24/1.15  fof(f7424,plain,(
% 6.24/1.15    ~r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK1),sK1)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f7370,f1220])).
% 6.24/1.15  fof(f1220,plain,(
% 6.24/1.15    ( ! [X4,X5,X3] : (~r2_hidden(sK3(k4_xboole_0(X3,X4),X5),X4) | r1_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 6.24/1.15    inference(resolution,[],[f182,f41])).
% 6.24/1.15  fof(f41,plain,(
% 6.24/1.15    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f3])).
% 6.24/1.15  fof(f3,axiom,(
% 6.24/1.15    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.24/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.24/1.15  fof(f182,plain,(
% 6.24/1.15    ( ! [X2,X0,X1] : (sP6(sK3(k4_xboole_0(X0,X1),X2),X1,X0) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 6.24/1.15    inference(resolution,[],[f46,f27])).
% 6.24/1.15  fof(f27,plain,(
% 6.24/1.15    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f16])).
% 6.24/1.15  fof(f16,plain,(
% 6.24/1.15    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.24/1.15    inference(ennf_transformation,[],[f13])).
% 6.24/1.15  fof(f13,plain,(
% 6.24/1.15    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.24/1.15    inference(rectify,[],[f5])).
% 6.24/1.15  fof(f5,axiom,(
% 6.24/1.15    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.24/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 6.24/1.15  fof(f46,plain,(
% 6.24/1.15    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP6(X3,X1,X0)) )),
% 6.24/1.15    inference(equality_resolution,[],[f43])).
% 6.24/1.15  fof(f43,plain,(
% 6.24/1.15    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.24/1.15    inference(cnf_transformation,[],[f3])).
% 6.24/1.15  fof(f7370,plain,(
% 6.24/1.15    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f457,f160,f7342,f366])).
% 6.24/1.15  fof(f366,plain,(
% 6.24/1.15    ( ! [X6,X8,X7,X9] : (~r2_hidden(X9,k2_xboole_0(X7,X8)) | ~r1_xboole_0(X6,X8) | ~r1_xboole_0(X6,X7) | ~r2_hidden(X9,X6)) )),
% 6.24/1.15    inference(resolution,[],[f38,f26])).
% 6.24/1.15  fof(f26,plain,(
% 6.24/1.15    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f16])).
% 6.24/1.15  fof(f38,plain,(
% 6.24/1.15    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f19])).
% 6.24/1.15  fof(f19,plain,(
% 6.24/1.15    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.24/1.15    inference(ennf_transformation,[],[f10])).
% 6.24/1.15  fof(f10,axiom,(
% 6.24/1.15    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.24/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 6.24/1.15  fof(f7342,plain,(
% 6.24/1.15    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 6.24/1.15    inference(duplicate_literal_removal,[],[f7323])).
% 6.24/1.15  fof(f7323,plain,(
% 6.24/1.15    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),sK2) | r1_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 6.24/1.15    inference(resolution,[],[f1221,f442])).
% 6.24/1.15  fof(f442,plain,(
% 6.24/1.15    ( ! [X1] : (~r2_hidden(sK3(X1,sK2),sK0) | r1_xboole_0(X1,sK2)) )),
% 6.24/1.15    inference(resolution,[],[f128,f28])).
% 6.24/1.15  fof(f28,plain,(
% 6.24/1.15    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f16])).
% 6.24/1.15  fof(f128,plain,(
% 6.24/1.15    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 6.24/1.15    inference(resolution,[],[f26,f21])).
% 6.24/1.15  fof(f21,plain,(
% 6.24/1.15    r1_xboole_0(sK0,sK2)),
% 6.24/1.15    inference(cnf_transformation,[],[f15])).
% 6.24/1.15  fof(f15,plain,(
% 6.24/1.15    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.24/1.15    inference(flattening,[],[f14])).
% 6.24/1.15  fof(f14,plain,(
% 6.24/1.15    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 6.24/1.15    inference(ennf_transformation,[],[f12])).
% 6.24/1.15  fof(f12,negated_conjecture,(
% 6.24/1.15    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 6.24/1.15    inference(negated_conjecture,[],[f11])).
% 6.24/1.15  fof(f11,conjecture,(
% 6.24/1.15    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 6.24/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 6.24/1.15  fof(f1221,plain,(
% 6.24/1.15    ( ! [X6,X8,X7] : (r2_hidden(sK3(k4_xboole_0(X6,X7),X8),X6) | r1_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 6.24/1.15    inference(resolution,[],[f182,f40])).
% 6.24/1.15  fof(f40,plain,(
% 6.24/1.15    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f3])).
% 6.24/1.15  fof(f160,plain,(
% 6.24/1.15    r2_hidden(sK4(sK0,sK1),k2_xboole_0(sK1,sK2))),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f20,f60,f30])).
% 6.24/1.15  fof(f30,plain,(
% 6.24/1.15    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f18])).
% 6.24/1.15  fof(f18,plain,(
% 6.24/1.15    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.24/1.15    inference(ennf_transformation,[],[f2])).
% 6.24/1.15  fof(f2,axiom,(
% 6.24/1.15    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.24/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 6.24/1.15  fof(f60,plain,(
% 6.24/1.15    r2_hidden(sK4(sK0,sK1),sK0)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f22,f31])).
% 6.24/1.15  fof(f31,plain,(
% 6.24/1.15    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f18])).
% 6.24/1.15  fof(f22,plain,(
% 6.24/1.15    ~r1_tarski(sK0,sK1)),
% 6.24/1.15    inference(cnf_transformation,[],[f15])).
% 6.24/1.15  fof(f20,plain,(
% 6.24/1.15    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 6.24/1.15    inference(cnf_transformation,[],[f15])).
% 6.24/1.15  fof(f457,plain,(
% 6.24/1.15    r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f238,f47])).
% 6.24/1.15  fof(f47,plain,(
% 6.24/1.15    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | ~sP6(X3,X1,X0)) )),
% 6.24/1.15    inference(equality_resolution,[],[f42])).
% 6.24/1.15  fof(f42,plain,(
% 6.24/1.15    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.24/1.15    inference(cnf_transformation,[],[f3])).
% 6.24/1.15  fof(f238,plain,(
% 6.24/1.15    sP6(sK4(sK0,sK1),sK1,sK0)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f60,f61,f39])).
% 6.24/1.15  fof(f39,plain,(
% 6.24/1.15    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f3])).
% 6.24/1.15  fof(f61,plain,(
% 6.24/1.15    ~r2_hidden(sK4(sK0,sK1),sK1)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f22,f32])).
% 6.24/1.15  fof(f32,plain,(
% 6.24/1.15    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.24/1.15    inference(cnf_transformation,[],[f18])).
% 6.24/1.15  fof(f7434,plain,(
% 6.24/1.15    r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK1),sK1)),
% 6.24/1.15    inference(unit_resulting_resolution,[],[f63,f7370,f165])).
% 6.24/1.15  fof(f165,plain,(
% 6.24/1.15    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4),X5) | ~r1_tarski(X4,X5) | r1_xboole_0(X3,X4)) )),
% 6.24/1.15    inference(resolution,[],[f30,f28])).
% 6.24/1.15  fof(f63,plain,(
% 6.24/1.15    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.24/1.15    inference(duplicate_literal_removal,[],[f62])).
% 6.24/1.15  fof(f62,plain,(
% 6.24/1.15    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 6.24/1.15    inference(resolution,[],[f32,f31])).
% 6.24/1.15  % SZS output end Proof for theBenchmark
% 6.24/1.16  % (5117)------------------------------
% 6.24/1.16  % (5117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.24/1.16  % (5117)Termination reason: Refutation
% 6.24/1.16  
% 6.24/1.16  % (5117)Memory used [KB]: 13304
% 6.24/1.16  % (5117)Time elapsed: 0.739 s
% 6.24/1.16  % (5117)------------------------------
% 6.24/1.16  % (5117)------------------------------
% 6.24/1.16  % (5130)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.24/1.16  % (5092)Success in time 0.808 s
%------------------------------------------------------------------------------
