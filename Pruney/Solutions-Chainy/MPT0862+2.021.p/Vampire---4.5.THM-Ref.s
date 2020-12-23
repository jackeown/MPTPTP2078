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
% DateTime   : Thu Dec  3 12:58:29 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  53 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 167 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f37,f51,f63])).

fof(f63,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f28,f11,f50,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f50,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_3
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f28,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_2
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f13,f48,f22])).

fof(f22,plain,
    ( spl4_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f13,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f11,f32])).

fof(f32,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),X0))
    | spl4_1 ),
    inference(forward_demodulation,[],[f31,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),X0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f24,f24,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f24,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f29,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f12,f26,f22])).

fof(f12,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803799040)
% 0.13/0.37  ipcrm: permission denied for id (809762817)
% 0.13/0.37  ipcrm: permission denied for id (803831810)
% 0.13/0.37  ipcrm: permission denied for id (803864580)
% 0.13/0.37  ipcrm: permission denied for id (806977541)
% 0.13/0.37  ipcrm: permission denied for id (803930118)
% 0.13/0.37  ipcrm: permission denied for id (807010311)
% 0.13/0.38  ipcrm: permission denied for id (803995657)
% 0.13/0.38  ipcrm: permission denied for id (809861130)
% 0.13/0.38  ipcrm: permission denied for id (807108619)
% 0.13/0.38  ipcrm: permission denied for id (807141388)
% 0.13/0.38  ipcrm: permission denied for id (807174157)
% 0.13/0.38  ipcrm: permission denied for id (807239695)
% 0.13/0.38  ipcrm: permission denied for id (809926672)
% 0.13/0.39  ipcrm: permission denied for id (807338001)
% 0.13/0.39  ipcrm: permission denied for id (807370770)
% 0.13/0.39  ipcrm: permission denied for id (811237395)
% 0.13/0.39  ipcrm: permission denied for id (807436308)
% 0.13/0.39  ipcrm: permission denied for id (804225045)
% 0.13/0.39  ipcrm: permission denied for id (804290582)
% 0.13/0.39  ipcrm: permission denied for id (804323351)
% 0.13/0.39  ipcrm: permission denied for id (804356120)
% 0.13/0.40  ipcrm: permission denied for id (807469081)
% 0.13/0.40  ipcrm: permission denied for id (807501850)
% 0.13/0.40  ipcrm: permission denied for id (804454427)
% 0.13/0.40  ipcrm: permission denied for id (804487196)
% 0.13/0.40  ipcrm: permission denied for id (807567390)
% 0.13/0.40  ipcrm: permission denied for id (804552735)
% 0.13/0.40  ipcrm: permission denied for id (807600160)
% 0.13/0.41  ipcrm: permission denied for id (804585505)
% 0.13/0.41  ipcrm: permission denied for id (810057763)
% 0.13/0.41  ipcrm: permission denied for id (810090532)
% 0.13/0.41  ipcrm: permission denied for id (804749350)
% 0.21/0.41  ipcrm: permission denied for id (807764007)
% 0.21/0.41  ipcrm: permission denied for id (807796776)
% 0.21/0.42  ipcrm: permission denied for id (807829545)
% 0.21/0.42  ipcrm: permission denied for id (804880426)
% 0.21/0.42  ipcrm: permission denied for id (807862315)
% 0.21/0.42  ipcrm: permission denied for id (804945964)
% 0.21/0.42  ipcrm: permission denied for id (804978733)
% 0.21/0.42  ipcrm: permission denied for id (805011502)
% 0.21/0.42  ipcrm: permission denied for id (805044271)
% 0.21/0.42  ipcrm: permission denied for id (811368496)
% 0.21/0.43  ipcrm: permission denied for id (807960625)
% 0.21/0.43  ipcrm: permission denied for id (810188850)
% 0.21/0.43  ipcrm: permission denied for id (811401267)
% 0.21/0.43  ipcrm: permission denied for id (808058932)
% 0.21/0.43  ipcrm: permission denied for id (805208117)
% 0.21/0.43  ipcrm: permission denied for id (808091702)
% 0.21/0.43  ipcrm: permission denied for id (810254391)
% 0.21/0.44  ipcrm: permission denied for id (805306425)
% 0.21/0.44  ipcrm: permission denied for id (811466810)
% 0.21/0.44  ipcrm: permission denied for id (810352699)
% 0.21/0.44  ipcrm: permission denied for id (805404732)
% 0.21/0.44  ipcrm: permission denied for id (810418237)
% 0.21/0.44  ipcrm: permission denied for id (808288318)
% 0.21/0.44  ipcrm: permission denied for id (811499583)
% 0.21/0.44  ipcrm: permission denied for id (808353856)
% 0.21/0.45  ipcrm: permission denied for id (810483777)
% 0.21/0.45  ipcrm: permission denied for id (805535810)
% 0.21/0.45  ipcrm: permission denied for id (810516547)
% 0.21/0.45  ipcrm: permission denied for id (808452164)
% 0.21/0.45  ipcrm: permission denied for id (808484933)
% 0.21/0.45  ipcrm: permission denied for id (808517702)
% 0.21/0.45  ipcrm: permission denied for id (810549319)
% 0.21/0.45  ipcrm: permission denied for id (805666888)
% 0.21/0.46  ipcrm: permission denied for id (805699657)
% 0.21/0.46  ipcrm: permission denied for id (808583242)
% 0.21/0.46  ipcrm: permission denied for id (805765195)
% 0.21/0.46  ipcrm: permission denied for id (805797964)
% 0.21/0.46  ipcrm: permission denied for id (805830733)
% 0.21/0.46  ipcrm: permission denied for id (805863503)
% 0.21/0.46  ipcrm: permission denied for id (805896272)
% 0.21/0.47  ipcrm: permission denied for id (805929041)
% 0.21/0.47  ipcrm: permission denied for id (810614866)
% 0.21/0.47  ipcrm: permission denied for id (810647635)
% 0.21/0.47  ipcrm: permission denied for id (808714324)
% 0.21/0.47  ipcrm: permission denied for id (805994581)
% 0.21/0.47  ipcrm: permission denied for id (810680406)
% 0.21/0.47  ipcrm: permission denied for id (806027351)
% 0.21/0.47  ipcrm: permission denied for id (808812632)
% 0.21/0.48  ipcrm: permission denied for id (806092889)
% 0.21/0.48  ipcrm: permission denied for id (808845402)
% 0.21/0.48  ipcrm: permission denied for id (811565147)
% 0.21/0.48  ipcrm: permission denied for id (808910940)
% 0.21/0.48  ipcrm: permission denied for id (810745949)
% 0.21/0.48  ipcrm: permission denied for id (806191198)
% 0.21/0.48  ipcrm: permission denied for id (806223967)
% 0.21/0.48  ipcrm: permission denied for id (808976480)
% 0.21/0.49  ipcrm: permission denied for id (810778721)
% 0.21/0.49  ipcrm: permission denied for id (806289506)
% 0.21/0.49  ipcrm: permission denied for id (811597923)
% 0.21/0.49  ipcrm: permission denied for id (809074788)
% 0.21/0.49  ipcrm: permission denied for id (806355045)
% 0.21/0.49  ipcrm: permission denied for id (810844262)
% 0.21/0.49  ipcrm: permission denied for id (810877031)
% 0.21/0.49  ipcrm: permission denied for id (809173096)
% 0.21/0.50  ipcrm: permission denied for id (809205865)
% 0.21/0.50  ipcrm: permission denied for id (809238634)
% 0.21/0.50  ipcrm: permission denied for id (806453355)
% 0.21/0.50  ipcrm: permission denied for id (811630700)
% 0.21/0.50  ipcrm: permission denied for id (809304173)
% 0.21/0.50  ipcrm: permission denied for id (809336942)
% 0.21/0.50  ipcrm: permission denied for id (809369711)
% 0.21/0.50  ipcrm: permission denied for id (809402480)
% 0.21/0.51  ipcrm: permission denied for id (806617203)
% 0.21/0.51  ipcrm: permission denied for id (809500788)
% 0.21/0.51  ipcrm: permission denied for id (809533557)
% 0.21/0.51  ipcrm: permission denied for id (809566326)
% 0.21/0.51  ipcrm: permission denied for id (806682743)
% 0.21/0.51  ipcrm: permission denied for id (806748280)
% 0.21/0.52  ipcrm: permission denied for id (806781049)
% 0.21/0.52  ipcrm: permission denied for id (809599098)
% 0.21/0.52  ipcrm: permission denied for id (811040892)
% 0.21/0.52  ipcrm: permission denied for id (811073661)
% 0.21/0.52  ipcrm: permission denied for id (806846590)
% 0.21/0.52  ipcrm: permission denied for id (811761791)
% 1.14/0.66  % (6574)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.14/0.66  % (6574)Refutation found. Thanks to Tanya!
% 1.14/0.66  % SZS status Theorem for theBenchmark
% 1.14/0.66  % (6573)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.14/0.66  % (6591)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.14/0.66  % (6564)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.14/0.67  % (6583)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.14/0.67  % (6566)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.14/0.67  % SZS output start Proof for theBenchmark
% 1.14/0.67  fof(f66,plain,(
% 1.14/0.67    $false),
% 1.14/0.67    inference(avatar_sat_refutation,[],[f29,f37,f51,f63])).
% 1.14/0.67  fof(f63,plain,(
% 1.14/0.67    spl4_2 | spl4_3),
% 1.14/0.67    inference(avatar_contradiction_clause,[],[f56])).
% 1.14/0.67  fof(f56,plain,(
% 1.14/0.67    $false | (spl4_2 | spl4_3)),
% 1.14/0.67    inference(unit_resulting_resolution,[],[f28,f11,f50,f17])).
% 1.14/0.67  fof(f17,plain,(
% 1.14/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 1.14/0.67    inference(cnf_transformation,[],[f8])).
% 1.14/0.67  fof(f8,plain,(
% 1.14/0.67    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 1.14/0.67    inference(ennf_transformation,[],[f3])).
% 1.14/0.67  fof(f3,axiom,(
% 1.14/0.67    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 1.14/0.67  fof(f50,plain,(
% 1.14/0.67    sK3 != k2_mcart_1(sK0) | spl4_3),
% 1.14/0.67    inference(avatar_component_clause,[],[f48])).
% 1.14/0.67  fof(f48,plain,(
% 1.14/0.67    spl4_3 <=> sK3 = k2_mcart_1(sK0)),
% 1.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.14/0.67  fof(f11,plain,(
% 1.14/0.67    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.14/0.67    inference(cnf_transformation,[],[f10])).
% 1.14/0.67  fof(f10,plain,(
% 1.14/0.67    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).
% 1.14/0.67  fof(f9,plain,(
% 1.14/0.67    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 1.14/0.67    introduced(choice_axiom,[])).
% 1.14/0.67  fof(f6,plain,(
% 1.14/0.67    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 1.14/0.67    inference(ennf_transformation,[],[f5])).
% 1.14/0.67  fof(f5,negated_conjecture,(
% 1.14/0.67    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.14/0.67    inference(negated_conjecture,[],[f4])).
% 1.14/0.67  fof(f4,conjecture,(
% 1.14/0.67    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 1.14/0.67  fof(f28,plain,(
% 1.14/0.67    sK2 != k2_mcart_1(sK0) | spl4_2),
% 1.14/0.67    inference(avatar_component_clause,[],[f26])).
% 1.14/0.67  fof(f26,plain,(
% 1.14/0.67    spl4_2 <=> sK2 = k2_mcart_1(sK0)),
% 1.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.14/0.67  fof(f51,plain,(
% 1.14/0.67    ~spl4_1 | ~spl4_3),
% 1.14/0.67    inference(avatar_split_clause,[],[f13,f48,f22])).
% 1.14/0.67  fof(f22,plain,(
% 1.14/0.67    spl4_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.14/0.67  fof(f13,plain,(
% 1.14/0.67    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.14/0.67    inference(cnf_transformation,[],[f10])).
% 1.14/0.67  fof(f37,plain,(
% 1.14/0.67    spl4_1),
% 1.14/0.67    inference(avatar_contradiction_clause,[],[f34])).
% 1.14/0.67  fof(f34,plain,(
% 1.14/0.67    $false | spl4_1),
% 1.14/0.67    inference(unit_resulting_resolution,[],[f11,f32])).
% 1.14/0.67  fof(f32,plain,(
% 1.14/0.67    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),X0))) ) | spl4_1),
% 1.14/0.67    inference(forward_demodulation,[],[f31,f18])).
% 1.14/0.67  fof(f18,plain,(
% 1.14/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.14/0.67    inference(cnf_transformation,[],[f1])).
% 1.14/0.67  fof(f1,axiom,(
% 1.14/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.14/0.67  fof(f31,plain,(
% 1.14/0.67    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),X0))) ) | spl4_1),
% 1.14/0.67    inference(unit_resulting_resolution,[],[f24,f24,f14])).
% 1.14/0.67  fof(f14,plain,(
% 1.14/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 1.14/0.67    inference(cnf_transformation,[],[f7])).
% 1.14/0.67  fof(f7,plain,(
% 1.14/0.67    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 1.14/0.67    inference(ennf_transformation,[],[f2])).
% 1.14/0.67  fof(f2,axiom,(
% 1.14/0.67    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 1.14/0.67  fof(f24,plain,(
% 1.14/0.67    sK1 != k1_mcart_1(sK0) | spl4_1),
% 1.14/0.67    inference(avatar_component_clause,[],[f22])).
% 1.14/0.67  fof(f29,plain,(
% 1.14/0.67    ~spl4_1 | ~spl4_2),
% 1.14/0.67    inference(avatar_split_clause,[],[f12,f26,f22])).
% 1.14/0.67  fof(f12,plain,(
% 1.14/0.67    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.14/0.67    inference(cnf_transformation,[],[f10])).
% 1.14/0.67  % SZS output end Proof for theBenchmark
% 1.14/0.67  % (6574)------------------------------
% 1.14/0.67  % (6574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.67  % (6574)Termination reason: Refutation
% 1.14/0.67  
% 1.14/0.67  % (6574)Memory used [KB]: 10618
% 1.14/0.67  % (6574)Time elapsed: 0.091 s
% 1.14/0.67  % (6574)------------------------------
% 1.14/0.67  % (6574)------------------------------
% 1.14/0.68  % (6422)Success in time 0.315 s
%------------------------------------------------------------------------------
