%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:13 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 118 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 334 expanded)
%              Number of equality atoms :   26 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f66,f72,f78,f84,f101,f106,f109])).

fof(f109,plain,
    ( spl5_1
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl5_1
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f107,f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f107,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(resolution,[],[f105,f83])).

fof(f83,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_13
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_17
  <=> ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,sK2))
        | ~ r2_hidden(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f106,plain,
    ( spl5_17
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f102,f99,f69,f104])).

fof(f69,plain,
    ( spl5_11
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f99,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,sK2))
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4,X1)
        | r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f97,f50,f27,f99])).

fof(f27,plain,
    ( spl5_2
  <=> sK0 = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f50,plain,
    ( spl5_7
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(superposition,[],[f51,f29])).

fof(f29,plain,
    ( sK0 = k4_tarski(sK3,sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f51,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f84,plain,
    ( spl5_13
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f79,f75,f37,f81])).

fof(f37,plain,
    ( spl5_4
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( spl5_12
  <=> k1_mcart_1(sK0) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f79,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f39,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f78,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f73,f46,f27,f75])).

fof(f46,plain,
    ( spl5_6
  <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f73,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f47,f29])).

fof(f47,plain,
    ( ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f72,plain,
    ( spl5_11
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f67,f63,f32,f69])).

fof(f32,plain,
    ( spl5_3
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f63,plain,
    ( spl5_10
  <=> k2_mcart_1(sK0) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f67,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(superposition,[],[f34,f65])).

fof(f65,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f34,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f66,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f61,f42,f27,f63])).

fof(f42,plain,
    ( spl5_5
  <=> ! [X1,X0] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f61,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f43,f29])).

fof(f43,plain,
    ( ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f48,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f44,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f12,f37])).

fof(f12,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    & sK0 = k4_tarski(sK3,sK4)
    & r2_hidden(k2_mcart_1(sK0),sK2)
    & r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        & ? [X3,X4] : k4_tarski(X3,X4) = X0
        & r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
      & ? [X4,X3] : k4_tarski(X3,X4) = sK0
      & r2_hidden(k2_mcart_1(sK0),sK2)
      & r2_hidden(k1_mcart_1(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X4,X3] : k4_tarski(X3,X4) = sK0
   => sK0 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f35,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    sK0 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1209237505)
% 0.13/0.37  ipcrm: permission denied for id (1209335812)
% 0.13/0.37  ipcrm: permission denied for id (1209368581)
% 0.13/0.38  ipcrm: permission denied for id (1209499657)
% 0.13/0.38  ipcrm: permission denied for id (1209532426)
% 0.13/0.39  ipcrm: permission denied for id (1209761809)
% 0.13/0.39  ipcrm: permission denied for id (1209794578)
% 0.13/0.39  ipcrm: permission denied for id (1209958423)
% 0.13/0.39  ipcrm: permission denied for id (1207959576)
% 0.13/0.40  ipcrm: permission denied for id (1209991193)
% 0.13/0.40  ipcrm: permission denied for id (1210023962)
% 0.13/0.40  ipcrm: permission denied for id (1207992347)
% 0.13/0.40  ipcrm: permission denied for id (1208057886)
% 0.13/0.41  ipcrm: permission denied for id (1210286116)
% 0.13/0.41  ipcrm: permission denied for id (1208123433)
% 0.13/0.42  ipcrm: permission denied for id (1210449962)
% 0.13/0.42  ipcrm: permission denied for id (1210548269)
% 0.13/0.42  ipcrm: permission denied for id (1208188974)
% 0.13/0.42  ipcrm: permission denied for id (1210613808)
% 0.13/0.42  ipcrm: permission denied for id (1210646577)
% 0.13/0.43  ipcrm: permission denied for id (1210679346)
% 0.20/0.43  ipcrm: permission denied for id (1210744884)
% 0.20/0.43  ipcrm: permission denied for id (1208320054)
% 0.20/0.43  ipcrm: permission denied for id (1208385594)
% 0.20/0.44  ipcrm: permission denied for id (1210908731)
% 0.20/0.44  ipcrm: permission denied for id (1210941500)
% 0.20/0.44  ipcrm: permission denied for id (1208418365)
% 0.20/0.44  ipcrm: permission denied for id (1208451136)
% 0.20/0.44  ipcrm: permission denied for id (1211039809)
% 0.20/0.44  ipcrm: permission denied for id (1211072578)
% 0.20/0.45  ipcrm: permission denied for id (1208516676)
% 0.20/0.45  ipcrm: permission denied for id (1211170886)
% 0.20/0.45  ipcrm: permission denied for id (1211236424)
% 0.20/0.45  ipcrm: permission denied for id (1211301962)
% 0.20/0.45  ipcrm: permission denied for id (1208680523)
% 0.20/0.46  ipcrm: permission denied for id (1211334732)
% 0.20/0.46  ipcrm: permission denied for id (1211367501)
% 0.20/0.46  ipcrm: permission denied for id (1208713294)
% 0.20/0.46  ipcrm: permission denied for id (1211400271)
% 0.20/0.46  ipcrm: permission denied for id (1208746065)
% 0.20/0.46  ipcrm: permission denied for id (1208778834)
% 0.20/0.47  ipcrm: permission denied for id (1211596887)
% 0.20/0.47  ipcrm: permission denied for id (1211629656)
% 0.20/0.47  ipcrm: permission denied for id (1211695194)
% 0.20/0.47  ipcrm: permission denied for id (1211727963)
% 0.20/0.47  ipcrm: permission denied for id (1211760732)
% 0.20/0.48  ipcrm: permission denied for id (1211859039)
% 0.20/0.48  ipcrm: permission denied for id (1211891808)
% 0.20/0.48  ipcrm: permission denied for id (1211924577)
% 0.20/0.48  ipcrm: permission denied for id (1211957346)
% 0.20/0.48  ipcrm: permission denied for id (1211990115)
% 0.20/0.49  ipcrm: permission denied for id (1212055653)
% 0.20/0.49  ipcrm: permission denied for id (1208811623)
% 0.20/0.49  ipcrm: permission denied for id (1212121192)
% 0.20/0.49  ipcrm: permission denied for id (1212219499)
% 0.20/0.49  ipcrm: permission denied for id (1212252268)
% 0.20/0.49  ipcrm: permission denied for id (1212285037)
% 0.20/0.50  ipcrm: permission denied for id (1212317806)
% 0.20/0.50  ipcrm: permission denied for id (1208942703)
% 0.20/0.50  ipcrm: permission denied for id (1212350576)
% 0.20/0.50  ipcrm: permission denied for id (1212383345)
% 0.20/0.50  ipcrm: permission denied for id (1212448883)
% 0.20/0.50  ipcrm: permission denied for id (1212514421)
% 0.20/0.51  ipcrm: permission denied for id (1212547190)
% 0.20/0.51  ipcrm: permission denied for id (1209172094)
% 0.61/0.57  % (18548)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.61/0.57  % (18549)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.61/0.58  % (18549)Refutation found. Thanks to Tanya!
% 0.61/0.58  % SZS status Theorem for theBenchmark
% 0.61/0.58  % SZS output start Proof for theBenchmark
% 0.61/0.58  fof(f110,plain,(
% 0.61/0.58    $false),
% 0.61/0.58    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f66,f72,f78,f84,f101,f106,f109])).
% 0.61/0.58  fof(f109,plain,(
% 0.61/0.58    spl5_1 | ~spl5_13 | ~spl5_17),
% 0.61/0.58    inference(avatar_contradiction_clause,[],[f108])).
% 0.61/0.58  fof(f108,plain,(
% 0.61/0.58    $false | (spl5_1 | ~spl5_13 | ~spl5_17)),
% 0.61/0.58    inference(subsumption_resolution,[],[f107,f24])).
% 0.61/0.58  fof(f24,plain,(
% 0.61/0.58    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl5_1),
% 0.61/0.58    inference(avatar_component_clause,[],[f22])).
% 0.61/0.58  fof(f22,plain,(
% 0.61/0.58    spl5_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.61/0.58  fof(f107,plain,(
% 0.61/0.58    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl5_13 | ~spl5_17)),
% 0.61/0.58    inference(resolution,[],[f105,f83])).
% 0.61/0.58  fof(f83,plain,(
% 0.61/0.58    r2_hidden(sK3,sK1) | ~spl5_13),
% 0.61/0.58    inference(avatar_component_clause,[],[f81])).
% 0.61/0.58  fof(f81,plain,(
% 0.61/0.58    spl5_13 <=> r2_hidden(sK3,sK1)),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.61/0.58  fof(f105,plain,(
% 0.61/0.58    ( ! [X0] : (~r2_hidden(sK3,X0) | r2_hidden(sK0,k2_zfmisc_1(X0,sK2))) ) | ~spl5_17),
% 0.61/0.58    inference(avatar_component_clause,[],[f104])).
% 0.61/0.58  fof(f104,plain,(
% 0.61/0.58    spl5_17 <=> ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK3,X0))),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.61/0.58  fof(f106,plain,(
% 0.61/0.58    spl5_17 | ~spl5_11 | ~spl5_16),
% 0.61/0.58    inference(avatar_split_clause,[],[f102,f99,f69,f104])).
% 0.61/0.58  fof(f69,plain,(
% 0.61/0.58    spl5_11 <=> r2_hidden(sK4,sK2)),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.61/0.58  fof(f99,plain,(
% 0.61/0.58    spl5_16 <=> ! [X1,X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X0))),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.61/0.58  fof(f102,plain,(
% 0.61/0.58    ( ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK3,X0)) ) | (~spl5_11 | ~spl5_16)),
% 0.61/0.58    inference(resolution,[],[f100,f71])).
% 0.61/0.58  fof(f71,plain,(
% 0.61/0.58    r2_hidden(sK4,sK2) | ~spl5_11),
% 0.61/0.58    inference(avatar_component_clause,[],[f69])).
% 0.61/0.58  fof(f100,plain,(
% 0.61/0.58    ( ! [X0,X1] : (~r2_hidden(sK4,X1) | r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK3,X0)) ) | ~spl5_16),
% 0.61/0.58    inference(avatar_component_clause,[],[f99])).
% 0.61/0.58  fof(f101,plain,(
% 0.61/0.58    spl5_16 | ~spl5_2 | ~spl5_7),
% 0.61/0.58    inference(avatar_split_clause,[],[f97,f50,f27,f99])).
% 0.61/0.58  fof(f27,plain,(
% 0.61/0.58    spl5_2 <=> sK0 = k4_tarski(sK3,sK4)),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.61/0.58  fof(f50,plain,(
% 0.61/0.58    spl5_7 <=> ! [X1,X3,X0,X2] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.61/0.58  fof(f97,plain,(
% 0.61/0.58    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X0)) ) | (~spl5_2 | ~spl5_7)),
% 0.61/0.58    inference(superposition,[],[f51,f29])).
% 0.61/0.58  fof(f29,plain,(
% 0.61/0.58    sK0 = k4_tarski(sK3,sK4) | ~spl5_2),
% 0.61/0.58    inference(avatar_component_clause,[],[f27])).
% 0.61/0.58  fof(f51,plain,(
% 0.61/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) ) | ~spl5_7),
% 0.61/0.58    inference(avatar_component_clause,[],[f50])).
% 0.61/0.58  fof(f84,plain,(
% 0.61/0.58    spl5_13 | ~spl5_4 | ~spl5_12),
% 0.61/0.58    inference(avatar_split_clause,[],[f79,f75,f37,f81])).
% 0.61/0.58  fof(f37,plain,(
% 0.61/0.58    spl5_4 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.61/0.58  fof(f75,plain,(
% 0.61/0.58    spl5_12 <=> k1_mcart_1(sK0) = sK3),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.61/0.58  fof(f79,plain,(
% 0.61/0.58    r2_hidden(sK3,sK1) | (~spl5_4 | ~spl5_12)),
% 0.61/0.58    inference(superposition,[],[f39,f77])).
% 0.61/0.58  fof(f77,plain,(
% 0.61/0.58    k1_mcart_1(sK0) = sK3 | ~spl5_12),
% 0.61/0.58    inference(avatar_component_clause,[],[f75])).
% 0.61/0.58  fof(f39,plain,(
% 0.61/0.58    r2_hidden(k1_mcart_1(sK0),sK1) | ~spl5_4),
% 0.61/0.58    inference(avatar_component_clause,[],[f37])).
% 0.61/0.58  fof(f78,plain,(
% 0.61/0.58    spl5_12 | ~spl5_2 | ~spl5_6),
% 0.61/0.58    inference(avatar_split_clause,[],[f73,f46,f27,f75])).
% 0.61/0.58  fof(f46,plain,(
% 0.61/0.58    spl5_6 <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.61/0.58  fof(f73,plain,(
% 0.61/0.58    k1_mcart_1(sK0) = sK3 | (~spl5_2 | ~spl5_6)),
% 0.61/0.58    inference(superposition,[],[f47,f29])).
% 0.61/0.58  fof(f47,plain,(
% 0.61/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) ) | ~spl5_6),
% 0.61/0.58    inference(avatar_component_clause,[],[f46])).
% 0.61/0.58  fof(f72,plain,(
% 0.61/0.58    spl5_11 | ~spl5_3 | ~spl5_10),
% 0.61/0.58    inference(avatar_split_clause,[],[f67,f63,f32,f69])).
% 0.61/0.58  fof(f32,plain,(
% 0.61/0.58    spl5_3 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.61/0.58  fof(f63,plain,(
% 0.61/0.58    spl5_10 <=> k2_mcart_1(sK0) = sK4),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.61/0.58  fof(f67,plain,(
% 0.61/0.58    r2_hidden(sK4,sK2) | (~spl5_3 | ~spl5_10)),
% 0.61/0.58    inference(superposition,[],[f34,f65])).
% 0.61/0.58  fof(f65,plain,(
% 0.61/0.58    k2_mcart_1(sK0) = sK4 | ~spl5_10),
% 0.61/0.58    inference(avatar_component_clause,[],[f63])).
% 0.61/0.58  fof(f34,plain,(
% 0.61/0.58    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl5_3),
% 0.61/0.58    inference(avatar_component_clause,[],[f32])).
% 0.61/0.58  fof(f66,plain,(
% 0.61/0.58    spl5_10 | ~spl5_2 | ~spl5_5),
% 0.61/0.58    inference(avatar_split_clause,[],[f61,f42,f27,f63])).
% 0.61/0.58  fof(f42,plain,(
% 0.61/0.58    spl5_5 <=> ! [X1,X0] : k2_mcart_1(k4_tarski(X0,X1)) = X1),
% 0.61/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.61/0.58  fof(f61,plain,(
% 0.61/0.58    k2_mcart_1(sK0) = sK4 | (~spl5_2 | ~spl5_5)),
% 0.61/0.58    inference(superposition,[],[f43,f29])).
% 0.61/0.58  fof(f43,plain,(
% 0.61/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) ) | ~spl5_5),
% 0.61/0.58    inference(avatar_component_clause,[],[f42])).
% 0.61/0.58  fof(f52,plain,(
% 0.61/0.58    spl5_7),
% 0.61/0.58    inference(avatar_split_clause,[],[f20,f50])).
% 0.61/0.58  fof(f20,plain,(
% 0.61/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.61/0.58    inference(cnf_transformation,[],[f11])).
% 0.61/0.58  fof(f11,plain,(
% 0.61/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.61/0.58    inference(flattening,[],[f10])).
% 0.61/0.58  fof(f10,plain,(
% 0.61/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.61/0.58    inference(nnf_transformation,[],[f1])).
% 0.61/0.58  fof(f1,axiom,(
% 0.61/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.61/0.58  fof(f48,plain,(
% 0.61/0.58    spl5_6),
% 0.61/0.58    inference(avatar_split_clause,[],[f16,f46])).
% 0.61/0.58  fof(f16,plain,(
% 0.61/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.61/0.58    inference(cnf_transformation,[],[f2])).
% 0.61/0.58  fof(f2,axiom,(
% 0.61/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.61/0.58  fof(f44,plain,(
% 0.61/0.58    spl5_5),
% 0.61/0.58    inference(avatar_split_clause,[],[f17,f42])).
% 0.61/0.58  fof(f17,plain,(
% 0.61/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.61/0.58    inference(cnf_transformation,[],[f2])).
% 0.61/0.58  fof(f40,plain,(
% 0.61/0.58    spl5_4),
% 0.61/0.58    inference(avatar_split_clause,[],[f12,f37])).
% 0.61/0.58  fof(f12,plain,(
% 0.61/0.58    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.61/0.58    inference(cnf_transformation,[],[f9])).
% 0.61/0.58  fof(f9,plain,(
% 0.61/0.58    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & sK0 = k4_tarski(sK3,sK4) & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).
% 0.61/0.58  fof(f7,plain,(
% 0.61/0.58    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & ? [X4,X3] : k4_tarski(X3,X4) = sK0 & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1))),
% 0.61/0.58    introduced(choice_axiom,[])).
% 0.61/0.58  fof(f8,plain,(
% 0.61/0.58    ? [X4,X3] : k4_tarski(X3,X4) = sK0 => sK0 = k4_tarski(sK3,sK4)),
% 0.61/0.58    introduced(choice_axiom,[])).
% 0.61/0.58  fof(f6,plain,(
% 0.61/0.58    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1))),
% 0.61/0.58    inference(flattening,[],[f5])).
% 0.61/0.58  fof(f5,plain,(
% 0.61/0.58    ? [X0,X1,X2] : ((~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0) & (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.61/0.58    inference(ennf_transformation,[],[f4])).
% 0.61/0.58  fof(f4,negated_conjecture,(
% 0.61/0.58    ~! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.61/0.58    inference(negated_conjecture,[],[f3])).
% 0.61/0.58  fof(f3,conjecture,(
% 0.61/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.61/0.58  fof(f35,plain,(
% 0.61/0.58    spl5_3),
% 0.61/0.58    inference(avatar_split_clause,[],[f13,f32])).
% 0.61/0.58  fof(f13,plain,(
% 0.61/0.58    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.61/0.58    inference(cnf_transformation,[],[f9])).
% 0.61/0.58  fof(f30,plain,(
% 0.61/0.58    spl5_2),
% 0.61/0.58    inference(avatar_split_clause,[],[f14,f27])).
% 0.61/0.58  fof(f14,plain,(
% 0.61/0.58    sK0 = k4_tarski(sK3,sK4)),
% 0.61/0.58    inference(cnf_transformation,[],[f9])).
% 0.61/0.58  fof(f25,plain,(
% 0.61/0.58    ~spl5_1),
% 0.61/0.58    inference(avatar_split_clause,[],[f15,f22])).
% 0.61/0.58  fof(f15,plain,(
% 0.61/0.58    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.61/0.58    inference(cnf_transformation,[],[f9])).
% 0.61/0.58  % SZS output end Proof for theBenchmark
% 0.61/0.58  % (18549)------------------------------
% 0.61/0.58  % (18549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.61/0.58  % (18549)Termination reason: Refutation
% 0.61/0.58  
% 0.61/0.58  % (18549)Memory used [KB]: 10618
% 0.61/0.58  % (18549)Time elapsed: 0.007 s
% 0.61/0.58  % (18549)------------------------------
% 0.61/0.58  % (18549)------------------------------
% 0.61/0.58  % (18546)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.61/0.58  % (18410)Success in time 0.221 s
%------------------------------------------------------------------------------
