%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:16 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 122 expanded)
%              Number of equality atoms :   36 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f57,f59,f65,f71])).

fof(f71,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f70,f62,f50])).

fof(f50,plain,
    ( spl4_2
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( spl4_4
  <=> r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,
    ( sK2 = k2_mcart_1(sK0)
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f22,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f64,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f60,f45,f62])).

fof(f45,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f17,f47])).

fof(f47,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f59,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f58,f45,f54])).

fof(f54,plain,
    ( spl4_3
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f16,f47])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f11,f54,f50])).

fof(f11,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f12,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (779026433)
% 0.13/0.37  ipcrm: permission denied for id (782368770)
% 0.13/0.37  ipcrm: permission denied for id (779059203)
% 0.13/0.37  ipcrm: permission denied for id (782401540)
% 0.13/0.37  ipcrm: permission denied for id (779091973)
% 0.13/0.38  ipcrm: permission denied for id (782499848)
% 0.13/0.38  ipcrm: permission denied for id (782532617)
% 0.13/0.38  ipcrm: permission denied for id (779288587)
% 0.13/0.38  ipcrm: permission denied for id (782598156)
% 0.13/0.39  ipcrm: permission denied for id (782663694)
% 0.13/0.39  ipcrm: permission denied for id (779354127)
% 0.13/0.39  ipcrm: permission denied for id (779386896)
% 0.13/0.39  ipcrm: permission denied for id (779419665)
% 0.13/0.40  ipcrm: permission denied for id (782729235)
% 0.13/0.40  ipcrm: permission denied for id (782794773)
% 0.21/0.40  ipcrm: permission denied for id (779649047)
% 0.21/0.41  ipcrm: permission denied for id (782893081)
% 0.21/0.41  ipcrm: permission denied for id (779747354)
% 0.21/0.41  ipcrm: permission denied for id (779812892)
% 0.21/0.41  ipcrm: permission denied for id (782991390)
% 0.21/0.42  ipcrm: permission denied for id (783122466)
% 0.21/0.42  ipcrm: permission denied for id (783155235)
% 0.21/0.42  ipcrm: permission denied for id (779976740)
% 0.21/0.42  ipcrm: permission denied for id (783188005)
% 0.21/0.43  ipcrm: permission denied for id (783220774)
% 0.21/0.43  ipcrm: permission denied for id (783286312)
% 0.21/0.43  ipcrm: permission denied for id (783319081)
% 0.21/0.43  ipcrm: permission denied for id (780107818)
% 0.21/0.43  ipcrm: permission denied for id (780140588)
% 0.21/0.44  ipcrm: permission denied for id (783384621)
% 0.21/0.44  ipcrm: permission denied for id (780271664)
% 0.21/0.44  ipcrm: permission denied for id (783515697)
% 0.21/0.44  ipcrm: permission denied for id (783548466)
% 0.21/0.45  ipcrm: permission denied for id (783581235)
% 0.21/0.45  ipcrm: permission denied for id (783646773)
% 0.21/0.45  ipcrm: permission denied for id (780435510)
% 0.21/0.45  ipcrm: permission denied for id (780468280)
% 0.21/0.45  ipcrm: permission denied for id (783712313)
% 0.21/0.46  ipcrm: permission denied for id (780501050)
% 0.21/0.46  ipcrm: permission denied for id (783745083)
% 0.21/0.46  ipcrm: permission denied for id (780533820)
% 0.21/0.46  ipcrm: permission denied for id (783777853)
% 0.21/0.46  ipcrm: permission denied for id (783810622)
% 0.21/0.46  ipcrm: permission denied for id (780599359)
% 0.21/0.47  ipcrm: permission denied for id (783941699)
% 0.21/0.47  ipcrm: permission denied for id (780664900)
% 0.21/0.47  ipcrm: permission denied for id (780697669)
% 0.21/0.47  ipcrm: permission denied for id (783974470)
% 0.21/0.48  ipcrm: permission denied for id (784040008)
% 0.21/0.48  ipcrm: permission denied for id (780795978)
% 0.21/0.48  ipcrm: permission denied for id (780828747)
% 0.21/0.48  ipcrm: permission denied for id (780861516)
% 0.21/0.49  ipcrm: permission denied for id (780959822)
% 0.21/0.49  ipcrm: permission denied for id (780992591)
% 0.21/0.49  ipcrm: permission denied for id (781025361)
% 0.21/0.49  ipcrm: permission denied for id (781090899)
% 0.21/0.49  ipcrm: permission denied for id (784203860)
% 0.21/0.50  ipcrm: permission denied for id (784236629)
% 0.21/0.50  ipcrm: permission denied for id (781189206)
% 0.21/0.50  ipcrm: permission denied for id (784269399)
% 0.21/0.50  ipcrm: permission denied for id (784302168)
% 0.21/0.50  ipcrm: permission denied for id (781320282)
% 0.21/0.50  ipcrm: permission denied for id (784367707)
% 0.21/0.51  ipcrm: permission denied for id (784400476)
% 0.21/0.51  ipcrm: permission denied for id (784433245)
% 0.21/0.51  ipcrm: permission denied for id (781418591)
% 0.21/0.51  ipcrm: permission denied for id (784498784)
% 0.21/0.51  ipcrm: permission denied for id (784531553)
% 0.21/0.51  ipcrm: permission denied for id (781516898)
% 0.21/0.51  ipcrm: permission denied for id (781549667)
% 0.21/0.51  ipcrm: permission denied for id (781582436)
% 0.21/0.51  ipcrm: permission denied for id (781647973)
% 0.21/0.52  ipcrm: permission denied for id (781713511)
% 0.21/0.52  ipcrm: permission denied for id (784597096)
% 0.21/0.52  ipcrm: permission denied for id (784629865)
% 0.21/0.52  ipcrm: permission denied for id (784662634)
% 0.21/0.52  ipcrm: permission denied for id (781844588)
% 0.21/0.52  ipcrm: permission denied for id (781942896)
% 0.21/0.52  ipcrm: permission denied for id (781975665)
% 0.21/0.53  ipcrm: permission denied for id (784924788)
% 0.21/0.53  ipcrm: permission denied for id (782041205)
% 0.21/0.53  ipcrm: permission denied for id (782073974)
% 0.21/0.53  ipcrm: permission denied for id (784957559)
% 0.21/0.53  ipcrm: permission denied for id (784990328)
% 0.21/0.53  ipcrm: permission denied for id (782205050)
% 0.21/0.53  ipcrm: permission denied for id (785055867)
% 0.21/0.54  ipcrm: permission denied for id (782270589)
% 0.21/0.54  ipcrm: permission denied for id (785121406)
% 1.00/0.69  % (18331)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.00/0.69  % (18339)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.00/0.70  % (18349)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.71  % (18349)Refutation not found, incomplete strategy% (18349)------------------------------
% 1.48/0.71  % (18349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.71  % (18349)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.71  
% 1.48/0.71  % (18349)Memory used [KB]: 1663
% 1.48/0.71  % (18349)Time elapsed: 0.060 s
% 1.48/0.71  % (18349)------------------------------
% 1.48/0.71  % (18349)------------------------------
% 1.48/0.71  % (18342)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.71  % (18342)Refutation found. Thanks to Tanya!
% 1.48/0.71  % SZS status Theorem for theBenchmark
% 1.48/0.71  % SZS output start Proof for theBenchmark
% 1.48/0.71  fof(f72,plain,(
% 1.48/0.71    $false),
% 1.48/0.71    inference(avatar_sat_refutation,[],[f48,f57,f59,f65,f71])).
% 1.48/0.71  fof(f71,plain,(
% 1.48/0.71    spl4_2 | ~spl4_4),
% 1.48/0.71    inference(avatar_split_clause,[],[f70,f62,f50])).
% 1.48/0.71  fof(f50,plain,(
% 1.48/0.71    spl4_2 <=> sK2 = k2_mcart_1(sK0)),
% 1.48/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.48/0.71  fof(f62,plain,(
% 1.48/0.71    spl4_4 <=> r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.48/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.48/0.71  fof(f70,plain,(
% 1.48/0.71    sK2 = k2_mcart_1(sK0) | ~spl4_4),
% 1.48/0.71    inference(duplicate_literal_removal,[],[f69])).
% 1.48/0.71  fof(f69,plain,(
% 1.48/0.71    sK2 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0) | ~spl4_4),
% 1.48/0.71    inference(resolution,[],[f64,f43])).
% 1.48/0.71  fof(f43,plain,(
% 1.48/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.48/0.71    inference(equality_resolution,[],[f32])).
% 1.48/0.71  fof(f32,plain,(
% 1.48/0.71    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.48/0.71    inference(definition_unfolding,[],[f22,f15])).
% 1.48/0.71  fof(f15,plain,(
% 1.48/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.48/0.71    inference(cnf_transformation,[],[f4])).
% 1.48/0.71  fof(f4,axiom,(
% 1.48/0.71    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.48/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.71  fof(f22,plain,(
% 1.48/0.71    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.48/0.71    inference(cnf_transformation,[],[f10])).
% 1.48/0.71  fof(f10,plain,(
% 1.48/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.48/0.71    inference(ennf_transformation,[],[f1])).
% 1.48/0.71  fof(f1,axiom,(
% 1.48/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.48/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.48/0.71  fof(f64,plain,(
% 1.48/0.71    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_4),
% 1.48/0.71    inference(avatar_component_clause,[],[f62])).
% 1.48/0.71  fof(f65,plain,(
% 1.48/0.71    spl4_4 | ~spl4_1),
% 1.48/0.71    inference(avatar_split_clause,[],[f60,f45,f62])).
% 1.48/0.71  fof(f45,plain,(
% 1.48/0.71    spl4_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 1.48/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.48/0.71  fof(f60,plain,(
% 1.48/0.71    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_1),
% 1.48/0.71    inference(resolution,[],[f17,f47])).
% 1.48/0.71  fof(f47,plain,(
% 1.48/0.71    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl4_1),
% 1.48/0.71    inference(avatar_component_clause,[],[f45])).
% 1.48/0.71  fof(f17,plain,(
% 1.48/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.48/0.71    inference(cnf_transformation,[],[f9])).
% 1.48/0.71  fof(f9,plain,(
% 1.48/0.71    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.48/0.71    inference(ennf_transformation,[],[f5])).
% 1.48/0.71  fof(f5,axiom,(
% 1.48/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.48/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.48/0.71  fof(f59,plain,(
% 1.48/0.71    spl4_3 | ~spl4_1),
% 1.48/0.71    inference(avatar_split_clause,[],[f58,f45,f54])).
% 1.48/0.71  fof(f54,plain,(
% 1.48/0.71    spl4_3 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.48/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.48/0.71  fof(f58,plain,(
% 1.48/0.71    r2_hidden(k1_mcart_1(sK0),sK1) | ~spl4_1),
% 1.48/0.71    inference(resolution,[],[f16,f47])).
% 1.48/0.71  fof(f16,plain,(
% 1.48/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.48/0.71    inference(cnf_transformation,[],[f9])).
% 1.48/0.71  fof(f57,plain,(
% 1.48/0.71    ~spl4_2 | ~spl4_3),
% 1.48/0.71    inference(avatar_split_clause,[],[f11,f54,f50])).
% 1.48/0.71  fof(f11,plain,(
% 1.48/0.71    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 1.48/0.71    inference(cnf_transformation,[],[f8])).
% 1.48/0.71  fof(f8,plain,(
% 1.48/0.71    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 1.48/0.71    inference(ennf_transformation,[],[f7])).
% 1.48/0.71  fof(f7,negated_conjecture,(
% 1.48/0.71    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.48/0.71    inference(negated_conjecture,[],[f6])).
% 1.48/0.72  fof(f6,conjecture,(
% 1.48/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.48/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 1.48/0.72  fof(f48,plain,(
% 1.48/0.72    spl4_1),
% 1.48/0.72    inference(avatar_split_clause,[],[f28,f45])).
% 1.48/0.72  fof(f28,plain,(
% 1.48/0.72    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 1.48/0.72    inference(definition_unfolding,[],[f12,f27])).
% 1.48/0.72  fof(f27,plain,(
% 1.48/0.72    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.72    inference(definition_unfolding,[],[f13,f26])).
% 1.48/0.72  fof(f26,plain,(
% 1.48/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/0.72    inference(definition_unfolding,[],[f14,f15])).
% 1.48/0.72  fof(f14,plain,(
% 1.48/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.72    inference(cnf_transformation,[],[f3])).
% 1.48/0.72  fof(f3,axiom,(
% 1.48/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.72  fof(f13,plain,(
% 1.48/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.72    inference(cnf_transformation,[],[f2])).
% 1.48/0.72  fof(f2,axiom,(
% 1.48/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.72  fof(f12,plain,(
% 1.48/0.72    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 1.48/0.72    inference(cnf_transformation,[],[f8])).
% 1.48/0.72  % SZS output end Proof for theBenchmark
% 1.48/0.72  % (18342)------------------------------
% 1.48/0.72  % (18342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.72  % (18342)Termination reason: Refutation
% 1.48/0.72  
% 1.48/0.72  % (18342)Memory used [KB]: 10618
% 1.48/0.72  % (18342)Time elapsed: 0.073 s
% 1.48/0.72  % (18342)------------------------------
% 1.48/0.72  % (18342)------------------------------
% 1.48/0.72  % (18333)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.72  % (18177)Success in time 0.36 s
%------------------------------------------------------------------------------
