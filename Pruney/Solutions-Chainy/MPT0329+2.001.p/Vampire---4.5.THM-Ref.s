%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:59 EST 2020

% Result     : Theorem 12.62s
% Output     : Refutation 13.21s
% Verified   : 
% Statistics : Number of formulae       :  633 (1646 expanded)
%              Number of leaves         :  140 ( 631 expanded)
%              Depth                    :   13
%              Number of atoms          : 1721 (5200 expanded)
%              Number of equality atoms :  564 (2344 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f291,f298,f306,f310,f318,f326,f334,f342,f352,f363,f368,f370,f379,f496,f503,f510,f519,f589,f2143,f6320,f6353,f6354,f6445,f6455,f6589,f6714,f6722,f6736,f6749,f7179,f7192,f7198,f7204,f7483,f7489,f7605,f7643,f7685,f7883,f7909,f9194,f9733,f9981,f9987,f9992,f10037,f10855,f10874,f10883,f10910,f10981,f10991,f11035,f11349,f11355,f11434,f11571,f11653,f11675,f11681,f12099,f12214,f12758,f12780,f12781,f13259,f13680,f13965,f13972,f14052,f14087,f14128,f14131,f14677,f14682,f14700,f14705,f15514,f18616,f18646,f19054,f19118,f19171,f19201,f19210,f20146,f20154,f20269,f20294,f20376,f20802,f20816,f20927,f20931,f21088,f21223,f21333,f21522,f21561,f21582,f22414,f22633,f22689,f24389,f24451,f24653,f24725,f25068,f25385])).

% (10051)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
fof(f25385,plain,
    ( spl9_6
    | spl9_15
    | spl9_11
    | spl9_9
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f25376,f7575,f316,f324,f340,f304])).

fof(f304,plain,
    ( spl9_6
  <=> sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f340,plain,
    ( spl9_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f324,plain,
    ( spl9_11
  <=> sK3 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f316,plain,
    ( spl9_9
  <=> sK3 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f7575,plain,
    ( spl9_77
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f25376,plain,
    ( sK3 = k1_tarski(sK2)
    | sK3 = k1_tarski(sK1)
    | k1_xboole_0 = sK3
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl9_77 ),
    inference(resolution,[],[f25239,f241])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0 ) ),
    inference(definition_unfolding,[],[f182,f130,f130])).

fof(f130,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f25239,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f7575])).

fof(f25068,plain,
    ( spl9_100
    | ~ spl9_99 ),
    inference(avatar_split_clause,[],[f25067,f7818,f7821])).

fof(f7821,plain,
    ( spl9_100
  <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f7818,plain,
    ( spl9_99
  <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f25067,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_99 ),
    inference(forward_demodulation,[],[f25066,f121])).

fof(f121,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25066,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_99 ),
    inference(forward_demodulation,[],[f25065,f394])).

fof(f394,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f127,f129])).

fof(f129,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f127,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f25065,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),sK3)))
    | ~ spl9_99 ),
    inference(forward_demodulation,[],[f25057,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f25057,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),sK3))
    | ~ spl9_99 ),
    inference(resolution,[],[f20042,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f20042,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_99 ),
    inference(avatar_component_clause,[],[f7818])).

fof(f24725,plain,
    ( ~ spl9_19
    | spl9_24
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f24724,f445,f437,f385])).

fof(f385,plain,
    ( spl9_19
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f437,plain,
    ( spl9_24
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f445,plain,
    ( spl9_25
  <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f24724,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),sK3)
    | spl9_24
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f438,f6603])).

fof(f6603,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f445])).

fof(f438,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))
    | spl9_24 ),
    inference(avatar_component_clause,[],[f437])).

fof(f24653,plain,
    ( spl9_22
    | ~ spl9_1
    | spl9_376 ),
    inference(avatar_split_clause,[],[f22191,f22141,f286,f419])).

fof(f419,plain,
    ( spl9_22
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f286,plain,
    ( spl9_1
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f22141,plain,
    ( spl9_376
  <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_376])])).

fof(f22191,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r2_hidden(sK2,sK3)
    | spl9_376 ),
    inference(superposition,[],[f22142,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f22142,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))
    | spl9_376 ),
    inference(avatar_component_clause,[],[f22141])).

fof(f24451,plain,
    ( spl9_207
    | ~ spl9_3
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(avatar_split_clause,[],[f24449,f22144,f7202,f7196,f293,f12097])).

fof(f12097,plain,
    ( spl9_207
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).

fof(f293,plain,
    ( spl9_3
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f7196,plain,
    ( spl9_65
  <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f7202,plain,
    ( spl9_66
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f22144,plain,
    ( spl9_377
  <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).

fof(f24449,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_3
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(forward_demodulation,[],[f24448,f392])).

fof(f392,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f129,f121])).

fof(f24448,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ spl9_3
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(forward_demodulation,[],[f24447,f8403])).

fof(f8403,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f159,f129])).

fof(f159,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f24447,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_xboole_0)))
    | ~ spl9_3
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(forward_demodulation,[],[f24446,f374])).

fof(f374,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f127,f121])).

fof(f24446,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))))
    | ~ spl9_3
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(forward_demodulation,[],[f24445,f12611])).

fof(f12611,plain,
    ( ! [X1] : k4_xboole_0(k2_xboole_0(k1_tarski(sK1),X1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(X1,k1_tarski(sK2)))
    | ~ spl9_65 ),
    inference(superposition,[],[f163,f7197])).

fof(f7197,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl9_65 ),
    inference(avatar_component_clause,[],[f7196])).

fof(f163,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f24445,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK2))))
    | ~ spl9_3
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(forward_demodulation,[],[f24411,f23825])).

fof(f23825,plain,
    ( ! [X2] : k2_xboole_0(k1_tarski(sK0),k4_xboole_0(X2,k1_tarski(sK2))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X2),k1_tarski(sK2))
    | ~ spl9_66 ),
    inference(superposition,[],[f163,f7203])).

fof(f7203,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f7202])).

fof(f24411,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK2)))
    | ~ spl9_3
    | ~ spl9_377 ),
    inference(superposition,[],[f14312,f22145])).

fof(f22145,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_377 ),
    inference(avatar_component_clause,[],[f22144])).

fof(f14312,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(sK3,X1),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),X1))
    | ~ spl9_3 ),
    inference(resolution,[],[f343,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f343,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f293])).

fof(f24389,plain,
    ( spl9_377
    | ~ spl9_376 ),
    inference(avatar_split_clause,[],[f24388,f22141,f22144])).

fof(f24388,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_376 ),
    inference(forward_demodulation,[],[f24387,f121])).

fof(f24387,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_376 ),
    inference(forward_demodulation,[],[f24386,f394])).

fof(f24386,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK2)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),sK3)))
    | ~ spl9_376 ),
    inference(forward_demodulation,[],[f24378,f160])).

fof(f24378,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK2)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),sK3))
    | ~ spl9_376 ),
    inference(resolution,[],[f24364,f135])).

fof(f24364,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))
    | ~ spl9_376 ),
    inference(avatar_component_clause,[],[f22141])).

fof(f22689,plain,
    ( ~ spl9_22
    | spl9_111 ),
    inference(avatar_split_clause,[],[f17359,f8261,f419])).

fof(f8261,plain,
    ( spl9_111
  <=> r1_tarski(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f17359,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl9_111 ),
    inference(resolution,[],[f10824,f16590])).

fof(f16590,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK3)
    | spl9_111 ),
    inference(avatar_component_clause,[],[f8261])).

fof(f10824,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f10816])).

fof(f10816,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f247,f211])).

fof(f211,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f123,f130])).

fof(f123,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f194,f130])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f22633,plain,
    ( spl9_2
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_36
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f22632,f6408,f6318,f445,f401,f289])).

fof(f289,plain,
    ( spl9_2
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f401,plain,
    ( spl9_21
  <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f6318,plain,
    ( spl9_36
  <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f6408,plain,
    ( spl9_43
  <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f22632,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_36
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f22631,f11147])).

fof(f11147,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f6408])).

fof(f22631,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_21
    | ~ spl9_25
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f22630,f21911])).

fof(f21911,plain,
    ( ! [X2] : k2_xboole_0(sK3,X2) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),X2))
    | ~ spl9_25 ),
    inference(superposition,[],[f159,f6603])).

fof(f22630,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl9_21
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f22586,f21931])).

fof(f21931,plain,
    ( ! [X2] : k2_xboole_0(sK3,X2) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),X2))
    | ~ spl9_21 ),
    inference(superposition,[],[f159,f6718])).

fof(f6718,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f401])).

fof(f22586,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl9_36 ),
    inference(superposition,[],[f8388,f6319])).

fof(f6319,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f6318])).

fof(f8388,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f159,f126])).

fof(f126,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f22414,plain,
    ( spl9_207
    | ~ spl9_354 ),
    inference(avatar_contradiction_clause,[],[f22413])).

fof(f22413,plain,
    ( $false
    | spl9_207
    | ~ spl9_354 ),
    inference(subsumption_resolution,[],[f21332,f22411])).

fof(f22411,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)))
    | spl9_207 ),
    inference(resolution,[],[f12098,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f167,f131])).

fof(f131,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f12098,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl9_207 ),
    inference(avatar_component_clause,[],[f12097])).

fof(f21332,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)))
    | ~ spl9_354 ),
    inference(avatar_component_clause,[],[f21331])).

fof(f21331,plain,
    ( spl9_354
  <=> r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).

fof(f21582,plain,
    ( ~ spl9_64
    | ~ spl9_81 ),
    inference(avatar_split_clause,[],[f7741,f7603,f7190])).

fof(f7190,plain,
    ( spl9_64
  <=> r2_hidden(sK0,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f7603,plain,
    ( spl9_81
  <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f7741,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl9_81 ),
    inference(superposition,[],[f831,f7604])).

fof(f7604,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0))
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f7603])).

fof(f831,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f266,f258])).

fof(f258,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f257])).

fof(f257,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f82,f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f266,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f98,f99])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f21561,plain,
    ( ~ spl9_91
    | spl9_84 ),
    inference(avatar_split_clause,[],[f14306,f7638,f7700])).

fof(f7700,plain,
    ( spl9_91
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f7638,plain,
    ( spl9_84
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f14306,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | spl9_84 ),
    inference(forward_demodulation,[],[f14304,f223])).

fof(f223,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f128,f130,f130])).

fof(f128,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f14304,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))
    | spl9_84 ),
    inference(resolution,[],[f7639,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f7639,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0))
    | spl9_84 ),
    inference(avatar_component_clause,[],[f7638])).

fof(f21522,plain,
    ( spl9_43
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f11807,f2141,f6408])).

fof(f2141,plain,
    ( spl9_32
  <=> sK3 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f11807,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_32 ),
    inference(superposition,[],[f129,f2142])).

fof(f2142,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK2),sK3)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f21333,plain,
    ( spl9_354
    | ~ spl9_197
    | ~ spl9_336 ),
    inference(avatar_split_clause,[],[f21329,f20798,f11347,f21331])).

fof(f11347,plain,
    ( spl9_197
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_197])])).

fof(f20798,plain,
    ( spl9_336
  <=> r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_336])])).

fof(f21329,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)))
    | ~ spl9_197
    | ~ spl9_336 ),
    inference(forward_demodulation,[],[f21328,f223])).

fof(f21328,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),sK3)))
    | ~ spl9_197
    | ~ spl9_336 ),
    inference(forward_demodulation,[],[f21327,f2135])).

fof(f2135,plain,(
    ! [X2,X1] : k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(resolution,[],[f134,f261])).

fof(f261,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_xboole_0(k1_tarski(X0),k1_tarski(X4))) ),
    inference(equality_resolution,[],[f260])).

fof(f260,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X4)) != X2 ) ),
    inference(equality_resolution,[],[f234])).

fof(f234,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2 ) ),
    inference(definition_unfolding,[],[f172,f130])).

fof(f172,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f93,f94])).

fof(f94,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f21327,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),sK3)))
    | ~ spl9_197
    | ~ spl9_336 ),
    inference(forward_demodulation,[],[f20799,f11348])).

fof(f11348,plain,
    ( sK0 = sK2
    | ~ spl9_197 ),
    inference(avatar_component_clause,[],[f11347])).

fof(f20799,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)))
    | ~ spl9_336 ),
    inference(avatar_component_clause,[],[f20798])).

fof(f21223,plain,
    ( spl9_18
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f6941,f385,f377])).

fof(f377,plain,
    ( spl9_18
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f6941,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl9_19 ),
    inference(superposition,[],[f127,f6719])).

fof(f6719,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f385])).

fof(f21088,plain,
    ( spl9_35
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f6741,f6345,f3386])).

fof(f3386,plain,
    ( spl9_35
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f6345,plain,
    ( spl9_38
  <=> r1_tarski(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f6741,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl9_38 ),
    inference(resolution,[],[f6346,f2961])).

fof(f2961,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f140,f258])).

fof(f140,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f78,f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f6346,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f6345])).

fof(f20931,plain,
    ( spl9_39
    | ~ spl9_1
    | spl9_99 ),
    inference(avatar_split_clause,[],[f7826,f7818,f286,f6349])).

fof(f6349,plain,
    ( spl9_39
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f7826,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r2_hidden(sK0,sK3)
    | spl9_99 ),
    inference(superposition,[],[f7819,f152])).

fof(f7819,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0)))
    | spl9_99 ),
    inference(avatar_component_clause,[],[f7818])).

fof(f20927,plain,
    ( spl9_35
    | ~ spl9_1
    | spl9_105 ),
    inference(avatar_split_clause,[],[f7919,f7911,f286,f3386])).

fof(f7911,plain,
    ( spl9_105
  <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f7919,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r2_hidden(sK1,sK3)
    | spl9_105 ),
    inference(superposition,[],[f7912,f152])).

fof(f7912,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))
    | spl9_105 ),
    inference(avatar_component_clause,[],[f7911])).

fof(f20816,plain,
    ( ~ spl9_207
    | spl9_235 ),
    inference(avatar_split_clause,[],[f14288,f14050,f12097])).

fof(f14050,plain,
    ( spl9_235
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).

fof(f14288,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl9_235 ),
    inference(forward_demodulation,[],[f14282,f223])).

fof(f14282,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | spl9_235 ),
    inference(resolution,[],[f14051,f168])).

fof(f14051,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0))
    | spl9_235 ),
    inference(avatar_component_clause,[],[f14050])).

fof(f20802,plain,
    ( spl9_336
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f20801,f293,f20798])).

fof(f20801,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)))
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f19869,f122])).

fof(f122,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f19869,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)))
    | ~ spl9_3 ),
    inference(superposition,[],[f14311,f374])).

fof(f14311,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),X0)))
    | ~ spl9_3 ),
    inference(resolution,[],[f343,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f165,f131,f131])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f20376,plain,
    ( k1_tarski(sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK1 != sK2
    | k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f20294,plain,
    ( sK1 != sK2
    | k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3)
    | k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f20269,plain,
    ( k1_tarski(sK0) != k4_xboole_0(sK3,k1_tarski(sK1))
    | sK3 != k4_xboole_0(sK3,k1_tarski(sK1))
    | sK3 = k1_tarski(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f20154,plain,
    ( ~ spl9_119
    | spl9_214 ),
    inference(avatar_split_clause,[],[f17358,f12366,f9178])).

fof(f9178,plain,
    ( spl9_119
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f12366,plain,
    ( spl9_214
  <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f17358,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl9_214 ),
    inference(resolution,[],[f10824,f13258])).

fof(f13258,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | spl9_214 ),
    inference(avatar_component_clause,[],[f12366])).

fof(f20146,plain,
    ( spl9_106
    | ~ spl9_105 ),
    inference(avatar_split_clause,[],[f18538,f7911,f7914])).

fof(f7914,plain,
    ( spl9_106
  <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f18538,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl9_105 ),
    inference(forward_demodulation,[],[f18537,f121])).

fof(f18537,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl9_105 ),
    inference(forward_demodulation,[],[f18536,f394])).

fof(f18536,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),sK3)))
    | ~ spl9_105 ),
    inference(forward_demodulation,[],[f18528,f160])).

fof(f18528,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK1)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),sK3))
    | ~ spl9_105 ),
    inference(resolution,[],[f18494,f135])).

fof(f18494,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_105 ),
    inference(avatar_component_clause,[],[f7911])).

fof(f19210,plain,
    ( spl9_38
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f6968,f424,f6345])).

fof(f424,plain,
    ( spl9_23
  <=> sK3 = k2_xboole_0(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f6968,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl9_23 ),
    inference(superposition,[],[f6894,f126])).

fof(f6894,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK1),k2_xboole_0(sK3,X0))
    | ~ spl9_23 ),
    inference(superposition,[],[f6568,f129])).

fof(f6568,plain,
    ( ! [X3] : r1_tarski(k1_tarski(sK1),k2_xboole_0(X3,sK3))
    | ~ spl9_23 ),
    inference(superposition,[],[f581,f6444])).

fof(f6444,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f424])).

fof(f581,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(resolution,[],[f550,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f550,plain,(
    ! [X2,X3] : r1_tarski(X3,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f521,f129])).

fof(f521,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f164,f255])).

fof(f255,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f19201,plain,
    ( spl9_25
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f6861,f424,f445])).

fof(f6861,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl9_23 ),
    inference(superposition,[],[f129,f6444])).

fof(f19171,plain,
    ( ~ spl9_3
    | spl9_88 ),
    inference(avatar_split_clause,[],[f13950,f7683,f293])).

fof(f7683,plain,
    ( spl9_88
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f13950,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_88 ),
    inference(resolution,[],[f7684,f168])).

fof(f7684,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl9_88 ),
    inference(avatar_component_clause,[],[f7683])).

fof(f19118,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) != k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f19054,plain,
    ( spl9_301
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62
    | ~ spl9_121 ),
    inference(avatar_split_clause,[],[f19050,f9192,f7167,f6318,f377,f19052])).

fof(f19052,plain,
    ( spl9_301
  <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_301])])).

fof(f7167,plain,
    ( spl9_62
  <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f9192,plain,
    ( spl9_121
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f19050,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62
    | ~ spl9_121 ),
    inference(forward_demodulation,[],[f19049,f121])).

fof(f19049,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k1_xboole_0))
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62
    | ~ spl9_121 ),
    inference(forward_demodulation,[],[f19048,f2136])).

fof(f2136,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(resolution,[],[f134,f263])).

fof(f263,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1))) ),
    inference(equality_resolution,[],[f262])).

fof(f262,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2 ) ),
    inference(equality_resolution,[],[f235])).

fof(f235,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2 ) ),
    inference(definition_unfolding,[],[f171,f130])).

fof(f171,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f95])).

fof(f19048,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k1_xboole_0)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62
    | ~ spl9_121 ),
    inference(forward_demodulation,[],[f19047,f378])).

fof(f378,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f377])).

fof(f19047,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK0),sK3)))
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62
    | ~ spl9_121 ),
    inference(forward_demodulation,[],[f18744,f9193])).

fof(f9193,plain,
    ( sK0 = sK1
    | ~ spl9_121 ),
    inference(avatar_component_clause,[],[f9192])).

fof(f18744,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK1),sK3)))
    | ~ spl9_18
    | ~ spl9_36
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f17555,f14279])).

fof(f14279,plain,
    ( ! [X0] : k2_xboole_0(k1_tarski(sK2),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,k1_tarski(sK2)),sK3)
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f14273,f129])).

fof(f14273,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_tarski(sK2)),sK3) = k2_xboole_0(k4_xboole_0(X0,sK3),k1_tarski(sK2))
    | ~ spl9_62 ),
    inference(superposition,[],[f163,f7168])).

fof(f7168,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f7167])).

fof(f17555,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3))
    | ~ spl9_18
    | ~ spl9_36 ),
    inference(superposition,[],[f6319,f14168])).

fof(f14168,plain,
    ( ! [X1] : k4_xboole_0(X1,sK3) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X1),sK3)
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f14162,f392])).

fof(f14162,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X1),sK3)
    | ~ spl9_18 ),
    inference(superposition,[],[f163,f378])).

fof(f18646,plain,
    ( sK3 != k4_xboole_0(sK3,k1_tarski(sK0))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f18616,plain,
    ( spl9_91
    | ~ spl9_3
    | ~ spl9_69
    | ~ spl9_106
    | ~ spl9_159 ),
    inference(avatar_split_clause,[],[f18614,f9957,f7914,f7487,f293,f7700])).

fof(f7487,plain,
    ( spl9_69
  <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f9957,plain,
    ( spl9_159
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).

fof(f18614,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ spl9_3
    | ~ spl9_69
    | ~ spl9_106
    | ~ spl9_159 ),
    inference(forward_demodulation,[],[f18613,f7488])).

fof(f7488,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f7487])).

fof(f18613,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | ~ spl9_3
    | ~ spl9_106
    | ~ spl9_159 ),
    inference(forward_demodulation,[],[f18612,f10583])).

fof(f10583,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f10496,f392])).

fof(f10496,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f163,f374])).

fof(f18612,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK1))))
    | ~ spl9_3
    | ~ spl9_106
    | ~ spl9_159 ),
    inference(forward_demodulation,[],[f18579,f10520])).

fof(f10520,plain,
    ( ! [X47] : k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X47),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(X47,k1_tarski(sK1)))
    | ~ spl9_159 ),
    inference(superposition,[],[f163,f9958])).

fof(f9958,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_159 ),
    inference(avatar_component_clause,[],[f9957])).

fof(f18579,plain,
    ( r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK1)))
    | ~ spl9_3
    | ~ spl9_106 ),
    inference(superposition,[],[f14312,f7915])).

fof(f7915,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f7914])).

fof(f15514,plain,(
    spl9_226 ),
    inference(avatar_contradiction_clause,[],[f15513])).

fof(f15513,plain,
    ( $false
    | spl9_226 ),
    inference(trivial_inequality_removal,[],[f15509])).

fof(f15509,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl9_226 ),
    inference(superposition,[],[f13964,f277])).

fof(f277,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(equality_resolution,[],[f251])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f198,f130])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f13964,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl9_226 ),
    inference(avatar_component_clause,[],[f13963])).

fof(f13963,plain,
    ( spl9_226
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).

fof(f14705,plain,(
    spl9_246 ),
    inference(avatar_contradiction_clause,[],[f14701])).

fof(f14701,plain,
    ( $false
    | spl9_246 ),
    inference(resolution,[],[f14699,f550])).

fof(f14699,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl9_246 ),
    inference(avatar_component_clause,[],[f14698])).

fof(f14698,plain,
    ( spl9_246
  <=> r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).

fof(f14700,plain,
    ( ~ spl9_246
    | spl9_43
    | ~ spl9_145 ),
    inference(avatar_split_clause,[],[f14689,f9437,f6408,f14698])).

fof(f9437,plain,
    ( spl9_145
  <=> r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f14689,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))
    | ~ spl9_145 ),
    inference(resolution,[],[f14673,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f14673,plain,
    ( r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)
    | ~ spl9_145 ),
    inference(avatar_component_clause,[],[f9437])).

fof(f14682,plain,(
    spl9_244 ),
    inference(avatar_contradiction_clause,[],[f14679])).

fof(f14679,plain,
    ( $false
    | spl9_244 ),
    inference(resolution,[],[f14676,f118])).

fof(f118,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f14676,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | spl9_244 ),
    inference(avatar_component_clause,[],[f14675])).

fof(f14675,plain,
    ( spl9_244
  <=> r1_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f14677,plain,
    ( spl9_145
    | ~ spl9_244
    | ~ spl9_21
    | ~ spl9_240 ),
    inference(avatar_split_clause,[],[f14662,f14115,f401,f14675,f9437])).

fof(f14115,plain,
    ( spl9_240
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f14662,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)
    | ~ spl9_21
    | ~ spl9_240 ),
    inference(superposition,[],[f14191,f14116])).

fof(f14116,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)
    | ~ spl9_240 ),
    inference(avatar_component_clause,[],[f14115])).

fof(f14191,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k4_xboole_0(X4,sK3),k1_tarski(sK0))
        | r1_tarski(X4,sK3) )
    | ~ spl9_21 ),
    inference(superposition,[],[f169,f6718])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f14131,plain,
    ( ~ spl9_91
    | spl9_92 ),
    inference(avatar_split_clause,[],[f7721,f7706,f7700])).

fof(f7706,plain,
    ( spl9_92
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f7721,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | spl9_92 ),
    inference(resolution,[],[f7707,f168])).

fof(f7707,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))
    | spl9_92 ),
    inference(avatar_component_clause,[],[f7706])).

fof(f14128,plain,
    ( spl9_79
    | ~ spl9_37
    | ~ spl9_39
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f8103,f7167,f6349,f6341,f7592])).

fof(f7592,plain,
    ( spl9_79
  <=> r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f6341,plain,
    ( spl9_37
  <=> r1_tarski(k1_tarski(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f8103,plain,
    ( r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2)))
    | ~ spl9_37
    | ~ spl9_39
    | ~ spl9_62 ),
    inference(superposition,[],[f7965,f7168])).

fof(f7965,plain,
    ( ! [X1] : r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k4_xboole_0(X1,sK3)))
    | ~ spl9_37
    | ~ spl9_39 ),
    inference(superposition,[],[f7313,f7150])).

fof(f7150,plain,
    ( ! [X21] : k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(X21,sK3))
    | ~ spl9_39 ),
    inference(resolution,[],[f154,f6611])).

fof(f6611,plain,
    ( ! [X1] : ~ r2_hidden(sK0,k4_xboole_0(X1,sK3))
    | ~ spl9_39 ),
    inference(resolution,[],[f6350,f266])).

fof(f6350,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f6349])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f7313,plain,
    ( ! [X41] : r1_tarski(k4_xboole_0(k1_tarski(sK0),X41),k4_xboole_0(sK3,X41))
    | ~ spl9_37 ),
    inference(resolution,[],[f166,f6342])).

fof(f6342,plain,
    ( r1_tarski(k1_tarski(sK0),sK3)
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f6341])).

fof(f14087,plain,
    ( spl9_22
    | spl9_13
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f12215,f7641,f332,f419])).

fof(f332,plain,
    ( spl9_13
  <=> sK3 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f7641,plain,
    ( spl9_85
  <=> k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f12215,plain,
    ( sK3 = k1_tarski(sK0)
    | r2_hidden(sK2,sK3)
    | ~ spl9_85 ),
    inference(superposition,[],[f7642,f152])).

fof(f7642,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f7641])).

fof(f14052,plain,
    ( ~ spl9_235
    | spl9_120
    | ~ spl9_194 ),
    inference(avatar_split_clause,[],[f12103,f11033,f9181,f14050])).

fof(f9181,plain,
    ( spl9_120
  <=> k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f11033,plain,
    ( spl9_194
  <=> r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).

fof(f12103,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK1))
    | ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0))
    | ~ spl9_194 ),
    inference(resolution,[],[f11034,f139])).

fof(f11034,plain,
    ( r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_194 ),
    inference(avatar_component_clause,[],[f11033])).

fof(f13972,plain,
    ( k1_tarski(sK2) != k4_xboole_0(sK3,k1_tarski(sK0))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0)))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13965,plain,
    ( ~ spl9_226
    | spl9_88
    | ~ spl9_218 ),
    inference(avatar_split_clause,[],[f13961,f12778,f7683,f13963])).

fof(f12778,plain,
    ( spl9_218
  <=> k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).

fof(f13961,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl9_88
    | ~ spl9_218 ),
    inference(forward_demodulation,[],[f13949,f12779])).

fof(f12779,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_218 ),
    inference(avatar_component_clause,[],[f12778])).

fof(f13949,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl9_88 ),
    inference(resolution,[],[f7684,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f13680,plain,
    ( spl9_223
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f13669,f437,f13678])).

fof(f13678,plain,
    ( spl9_223
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_223])])).

fof(f13669,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3)
    | ~ spl9_24 ),
    inference(superposition,[],[f394,f11550])).

fof(f11550,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f437])).

fof(f13259,plain,
    ( spl9_38
    | ~ spl9_214
    | ~ spl9_21
    | ~ spl9_203 ),
    inference(avatar_split_clause,[],[f13254,f11651,f401,f12366,f6345])).

fof(f11651,plain,
    ( spl9_203
  <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_203])])).

fof(f13254,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl9_21
    | ~ spl9_203 ),
    inference(superposition,[],[f11275,f11652])).

fof(f11652,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3)
    | ~ spl9_203 ),
    inference(avatar_component_clause,[],[f11651])).

fof(f11275,plain,
    ( ! [X16] :
        ( ~ r1_tarski(k4_xboole_0(X16,sK3),k1_tarski(sK0))
        | r1_tarski(X16,sK3) )
    | ~ spl9_21 ),
    inference(superposition,[],[f169,f6718])).

fof(f12781,plain,
    ( ~ spl9_92
    | spl9_218
    | ~ spl9_216 ),
    inference(avatar_split_clause,[],[f12764,f12756,f12778,f7706])).

fof(f12756,plain,
    ( spl9_216
  <=> r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f12764,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))
    | ~ spl9_216 ),
    inference(resolution,[],[f12757,f139])).

fof(f12757,plain,
    ( r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_216 ),
    inference(avatar_component_clause,[],[f12756])).

fof(f12780,plain,
    ( spl9_218
    | ~ spl9_4
    | ~ spl9_216 ),
    inference(avatar_split_clause,[],[f12776,f12756,f296,f12778])).

fof(f296,plain,
    ( spl9_4
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f12776,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_4
    | ~ spl9_216 ),
    inference(forward_demodulation,[],[f12775,f121])).

fof(f12775,plain,
    ( k2_xboole_0(k1_tarski(sK2),k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_4
    | ~ spl9_216 ),
    inference(forward_demodulation,[],[f12774,f374])).

fof(f12774,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK3,sK3))
    | ~ spl9_4
    | ~ spl9_216 ),
    inference(forward_demodulation,[],[f12773,f350])).

fof(f350,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f296])).

fof(f12773,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | ~ spl9_216 ),
    inference(forward_demodulation,[],[f12763,f160])).

fof(f12763,plain,
    ( k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2)))
    | ~ spl9_216 ),
    inference(resolution,[],[f12757,f135])).

fof(f12758,plain,
    ( spl9_216
    | ~ spl9_81
    | ~ spl9_111 ),
    inference(avatar_split_clause,[],[f12739,f8261,f7603,f12756])).

fof(f12739,plain,
    ( r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_81
    | ~ spl9_111 ),
    inference(superposition,[],[f11658,f7604])).

fof(f11658,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k1_tarski(sK2),X0),k4_xboole_0(sK3,X0))
    | ~ spl9_111 ),
    inference(resolution,[],[f8262,f166])).

fof(f8262,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl9_111 ),
    inference(avatar_component_clause,[],[f8261])).

fof(f12214,plain,
    ( ~ spl9_210
    | spl9_207 ),
    inference(avatar_split_clause,[],[f12210,f12097,f12212])).

fof(f12212,plain,
    ( spl9_210
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f12210,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl9_207 ),
    inference(resolution,[],[f12098,f147])).

fof(f12099,plain,
    ( ~ spl9_207
    | spl9_166 ),
    inference(avatar_split_clause,[],[f12090,f10035,f12097])).

fof(f10035,plain,
    ( spl9_166
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f12090,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl9_166 ),
    inference(resolution,[],[f10036,f168])).

fof(f10036,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1))
    | spl9_166 ),
    inference(avatar_component_clause,[],[f10035])).

fof(f11681,plain,
    ( spl9_205
    | ~ spl9_63 ),
    inference(avatar_split_clause,[],[f11670,f7186,f11679])).

fof(f11679,plain,
    ( spl9_205
  <=> k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_205])])).

fof(f7186,plain,
    ( spl9_63
  <=> r2_hidden(sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f11670,plain,
    ( k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl9_63 ),
    inference(resolution,[],[f11338,f134])).

fof(f11338,plain,
    ( r2_hidden(sK1,k1_tarski(sK2))
    | ~ spl9_63 ),
    inference(avatar_component_clause,[],[f7186])).

fof(f11675,plain,
    ( spl9_204
    | ~ spl9_63 ),
    inference(avatar_split_clause,[],[f11666,f7186,f11673])).

fof(f11673,plain,
    ( spl9_204
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).

fof(f11666,plain,
    ( sK1 = sK2
    | ~ spl9_63 ),
    inference(resolution,[],[f11338,f259])).

fof(f259,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f11653,plain,
    ( spl9_203
    | spl9_35 ),
    inference(avatar_split_clause,[],[f11648,f3386,f11651])).

fof(f11648,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3)
    | spl9_35 ),
    inference(resolution,[],[f11591,f154])).

fof(f11591,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl9_35 ),
    inference(avatar_component_clause,[],[f3386])).

fof(f11571,plain,
    ( spl9_111
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f11315,f296,f8261])).

fof(f11315,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl9_4 ),
    inference(superposition,[],[f269,f350])).

fof(f269,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f185,f130])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f102])).

fof(f11434,plain,
    ( sK0 != sK2
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))
    | sK3 = k1_tarski(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f11355,plain,
    ( spl9_198
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f11344,f7596,f11353])).

fof(f11353,plain,
    ( spl9_198
  <=> k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).

fof(f7596,plain,
    ( spl9_80
  <=> r2_hidden(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f11344,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))
    | ~ spl9_80 ),
    inference(resolution,[],[f11336,f134])).

fof(f11336,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f7596])).

fof(f11349,plain,
    ( spl9_197
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f11340,f7596,f11347])).

fof(f11340,plain,
    ( sK0 = sK2
    | ~ spl9_80 ),
    inference(resolution,[],[f11336,f259])).

fof(f11035,plain,
    ( spl9_194
    | ~ spl9_37
    | ~ spl9_159 ),
    inference(avatar_split_clause,[],[f10139,f9957,f6341,f11033])).

fof(f10139,plain,
    ( r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_37
    | ~ spl9_159 ),
    inference(superposition,[],[f7313,f9958])).

fof(f10991,plain,
    ( spl9_37
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f6947,f385,f6341])).

fof(f6947,plain,
    ( r1_tarski(k1_tarski(sK0),sK3)
    | ~ spl9_19 ),
    inference(superposition,[],[f550,f6719])).

fof(f10981,plain,
    ( spl9_21
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f6930,f385,f401])).

fof(f6930,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl9_19 ),
    inference(superposition,[],[f6719,f129])).

fof(f10910,plain,
    ( k1_tarski(sK0) != k4_xboole_0(sK3,k1_tarski(sK1))
    | k1_tarski(sK1) != k4_xboole_0(sK3,k1_tarski(sK0))
    | sK3 != k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1))))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f10883,plain,
    ( ~ spl9_7
    | spl9_172 ),
    inference(avatar_contradiction_clause,[],[f10879])).

fof(f10879,plain,
    ( $false
    | ~ spl9_7
    | spl9_172 ),
    inference(resolution,[],[f10854,f6781])).

fof(f6781,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK3,X0))
    | ~ spl9_7 ),
    inference(superposition,[],[f6331,f129])).

fof(f6331,plain,
    ( ! [X3] : r2_hidden(sK0,k2_xboole_0(X3,sK3))
    | ~ spl9_7 ),
    inference(superposition,[],[f2970,f348])).

fof(f348,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl9_7
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2970,plain,(
    ! [X10,X8,X9] : r2_hidden(X8,k2_xboole_0(X9,k2_xboole_0(k1_tarski(X8),X10))) ),
    inference(resolution,[],[f2961,f581])).

fof(f10854,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl9_172 ),
    inference(avatar_component_clause,[],[f10853])).

fof(f10853,plain,
    ( spl9_172
  <=> r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f10874,plain,
    ( ~ spl9_23
    | spl9_171 ),
    inference(avatar_contradiction_clause,[],[f10870])).

fof(f10870,plain,
    ( $false
    | ~ spl9_23
    | spl9_171 ),
    inference(resolution,[],[f10851,f6808])).

fof(f6808,plain,
    ( ! [X0] : r2_hidden(sK1,k2_xboole_0(sK3,X0))
    | ~ spl9_23 ),
    inference(superposition,[],[f6558,f129])).

fof(f6558,plain,
    ( ! [X0] : r2_hidden(sK1,k2_xboole_0(X0,sK3))
    | ~ spl9_23 ),
    inference(superposition,[],[f2970,f6444])).

fof(f10851,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl9_171 ),
    inference(avatar_component_clause,[],[f10850])).

fof(f10850,plain,
    ( spl9_171
  <=> r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_171])])).

fof(f10855,plain,
    ( ~ spl9_171
    | ~ spl9_172
    | spl9_3
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f10848,f308,f293,f10853,f10850])).

fof(f10848,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f10847,f8394])).

fof(f8394,plain,
    ( ! [X18] : k2_xboole_0(sK3,X18) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X18))
    | ~ spl9_7 ),
    inference(superposition,[],[f159,f348])).

fof(f10847,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2)))
    | ~ r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_3
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f10833,f8394])).

fof(f10833,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_3
    | ~ spl9_7 ),
    inference(resolution,[],[f10819,f294])).

fof(f294,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f293])).

fof(f10819,plain,
    ( ! [X8] :
        ( r1_tarski(sK3,X8)
        | ~ r2_hidden(sK1,X8)
        | ~ r2_hidden(sK0,X8) )
    | ~ spl9_7 ),
    inference(superposition,[],[f247,f348])).

fof(f10037,plain,
    ( ~ spl9_166
    | spl9_165
    | ~ spl9_161 ),
    inference(avatar_split_clause,[],[f10021,f9979,f10031,f10035])).

fof(f10031,plain,
    ( spl9_165
  <=> k1_tarski(sK1) = k4_xboole_0(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).

fof(f9979,plain,
    ( spl9_161
  <=> r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).

fof(f10021,plain,
    ( k1_tarski(sK1) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1))
    | ~ spl9_161 ),
    inference(resolution,[],[f9980,f139])).

fof(f9980,plain,
    ( r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_161 ),
    inference(avatar_component_clause,[],[f9979])).

fof(f9992,plain,
    ( spl9_159
    | spl9_162 ),
    inference(avatar_split_clause,[],[f9989,f9984,f9957])).

fof(f9984,plain,
    ( spl9_162
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f9989,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl9_162 ),
    inference(resolution,[],[f9985,f154])).

fof(f9985,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl9_162 ),
    inference(avatar_component_clause,[],[f9984])).

fof(f9987,plain,
    ( ~ spl9_162
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f9972,f9731,f9984])).

fof(f9731,plain,
    ( spl9_154
  <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f9972,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl9_154 ),
    inference(superposition,[],[f831,f9732])).

fof(f9732,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f9731])).

fof(f9981,plain,
    ( spl9_161
    | ~ spl9_38
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f9966,f9731,f6345,f9979])).

fof(f9966,plain,
    ( r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_38
    | ~ spl9_154 ),
    inference(superposition,[],[f7314,f9732])).

fof(f7314,plain,
    ( ! [X42] : r1_tarski(k4_xboole_0(k1_tarski(sK1),X42),k4_xboole_0(sK3,X42))
    | ~ spl9_38 ),
    inference(resolution,[],[f166,f6346])).

fof(f9733,plain,
    ( spl9_154
    | spl9_119 ),
    inference(avatar_split_clause,[],[f9264,f9178,f9731])).

fof(f9264,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl9_119 ),
    inference(resolution,[],[f9261,f154])).

fof(f9261,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl9_119 ),
    inference(avatar_component_clause,[],[f9178])).

fof(f9194,plain,
    ( spl9_121
    | ~ spl9_119 ),
    inference(avatar_split_clause,[],[f9185,f9178,f9192])).

fof(f9185,plain,
    ( sK0 = sK1
    | ~ spl9_119 ),
    inference(resolution,[],[f9179,f259])).

fof(f9179,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl9_119 ),
    inference(avatar_component_clause,[],[f9178])).

fof(f7909,plain,
    ( spl9_104
    | ~ spl9_103 ),
    inference(avatar_split_clause,[],[f7900,f7881,f7907])).

fof(f7907,plain,
    ( spl9_104
  <=> sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f7881,plain,
    ( spl9_103
  <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f7900,plain,
    ( sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1))))
    | ~ spl9_103 ),
    inference(resolution,[],[f7882,f135])).

fof(f7882,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3)
    | ~ spl9_103 ),
    inference(avatar_component_clause,[],[f7881])).

fof(f7883,plain,
    ( spl9_103
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f7872,f6747,f7881])).

fof(f6747,plain,
    ( spl9_58
  <=> sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f7872,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3)
    | ~ spl9_58 ),
    inference(superposition,[],[f521,f6748])).

fof(f6748,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f6747])).

fof(f7685,plain,
    ( ~ spl9_88
    | spl9_3 ),
    inference(avatar_split_clause,[],[f7657,f293,f7683])).

fof(f7657,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl9_3 ),
    inference(resolution,[],[f169,f294])).

fof(f7643,plain,
    ( ~ spl9_84
    | spl9_85
    | ~ spl9_79 ),
    inference(avatar_split_clause,[],[f7622,f7592,f7641,f7638])).

fof(f7622,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0))
    | ~ spl9_79 ),
    inference(resolution,[],[f7593,f139])).

fof(f7593,plain,
    ( r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2)))
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f7592])).

fof(f7605,plain,
    ( spl9_81
    | spl9_80 ),
    inference(avatar_split_clause,[],[f7600,f7596,f7603])).

fof(f7600,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0))
    | spl9_80 ),
    inference(resolution,[],[f7597,f154])).

fof(f7597,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK0))
    | spl9_80 ),
    inference(avatar_component_clause,[],[f7596])).

fof(f7489,plain,
    ( spl9_69
    | spl9_68 ),
    inference(avatar_split_clause,[],[f7484,f7480,f7487])).

fof(f7480,plain,
    ( spl9_68
  <=> r2_hidden(sK2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f7484,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))
    | spl9_68 ),
    inference(resolution,[],[f7481,f154])).

fof(f7481,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK1))
    | spl9_68 ),
    inference(avatar_component_clause,[],[f7480])).

fof(f7483,plain,
    ( ~ spl9_68
    | ~ spl9_65 ),
    inference(avatar_split_clause,[],[f7472,f7196,f7480])).

fof(f7472,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK1))
    | ~ spl9_65 ),
    inference(superposition,[],[f831,f7197])).

fof(f7204,plain,
    ( spl9_66
    | spl9_64 ),
    inference(avatar_split_clause,[],[f7199,f7190,f7202])).

fof(f7199,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl9_64 ),
    inference(resolution,[],[f7191,f154])).

fof(f7191,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | spl9_64 ),
    inference(avatar_component_clause,[],[f7190])).

fof(f7198,plain,
    ( spl9_65
    | spl9_63 ),
    inference(avatar_split_clause,[],[f7193,f7186,f7196])).

fof(f7193,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl9_63 ),
    inference(resolution,[],[f7187,f154])).

fof(f7187,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK2))
    | spl9_63 ),
    inference(avatar_component_clause,[],[f7186])).

fof(f7192,plain,
    ( ~ spl9_64
    | ~ spl9_39
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f7183,f7167,f6349,f7190])).

fof(f7183,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl9_39
    | ~ spl9_62 ),
    inference(superposition,[],[f6611,f7168])).

fof(f7179,plain,
    ( spl9_62
    | spl9_22 ),
    inference(avatar_split_clause,[],[f7163,f419,f7167])).

fof(f7163,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)
    | spl9_22 ),
    inference(resolution,[],[f154,f6660])).

fof(f6660,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f419])).

fof(f6749,plain,
    ( spl9_58
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f6742,f6345,f6747])).

fof(f6742,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1)))
    | ~ spl9_38 ),
    inference(resolution,[],[f6346,f135])).

fof(f6736,plain,
    ( spl9_56
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f6729,f6341,f6734])).

fof(f6734,plain,
    ( spl9_56
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f6729,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl9_37 ),
    inference(resolution,[],[f6342,f135])).

fof(f6722,plain,
    ( spl9_19
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f6610,f6349,f385])).

fof(f6610,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl9_39 ),
    inference(resolution,[],[f6350,f134])).

fof(f6714,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f6712])).

fof(f6712,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f330,f550])).

fof(f330,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl9_12
  <=> r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f6589,plain,(
    spl9_10 ),
    inference(avatar_contradiction_clause,[],[f6587])).

fof(f6587,plain,
    ( $false
    | spl9_10 ),
    inference(resolution,[],[f322,f581])).

fof(f322,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2))))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl9_10
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f6455,plain,
    ( spl9_39
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f6454,f377,f6349])).

fof(f6454,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl9_18 ),
    inference(trivial_inequality_removal,[],[f6452])).

fof(f6452,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,sK3)
    | ~ spl9_18 ),
    inference(superposition,[],[f149,f378])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f6445,plain,
    ( spl9_23
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f6434,f3386,f424])).

fof(f6434,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),sK3)
    | ~ spl9_35 ),
    inference(resolution,[],[f3387,f134])).

fof(f3387,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f3386])).

fof(f6354,plain,
    ( spl9_39
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f6333,f308,f6349])).

fof(f6333,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl9_7 ),
    inference(superposition,[],[f2968,f348])).

fof(f2968,plain,(
    ! [X4,X3] : r2_hidden(X3,k2_xboole_0(k1_tarski(X3),X4)) ),
    inference(resolution,[],[f2961,f550])).

fof(f6353,plain,
    ( spl9_35
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f6329,f308,f3386])).

fof(f6329,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl9_7 ),
    inference(superposition,[],[f2967,f348])).

fof(f2967,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X1))) ),
    inference(resolution,[],[f2961,f521])).

fof(f6320,plain,
    ( spl9_36
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f6252,f293,f6318])).

fof(f6252,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))
    | ~ spl9_3 ),
    inference(resolution,[],[f135,f343])).

fof(f2143,plain,
    ( spl9_32
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f2138,f419,f2141])).

fof(f2138,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK2),sK3)
    | ~ spl9_22 ),
    inference(resolution,[],[f134,f420])).

fof(f420,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f419])).

fof(f589,plain,(
    spl9_16 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | spl9_16 ),
    inference(subsumption_resolution,[],[f362,f581])).

fof(f362,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))))
    | spl9_16 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl9_16
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f519,plain,
    ( spl9_31
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f514,f293,f517])).

fof(f517,plain,
    ( spl9_31
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f514,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl9_3 ),
    inference(resolution,[],[f148,f343])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f85])).

fof(f510,plain,(
    spl9_29 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl9_29 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl9_29 ),
    inference(superposition,[],[f502,f127])).

fof(f502,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))
    | spl9_29 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl9_29
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f503,plain,
    ( ~ spl9_29
    | spl9_17 ),
    inference(avatar_split_clause,[],[f497,f366,f501])).

fof(f366,plain,
    ( spl9_17
  <=> r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f497,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))
    | spl9_17 ),
    inference(resolution,[],[f147,f367])).

fof(f367,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f366])).

fof(f496,plain,(
    spl9_14 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | spl9_14 ),
    inference(resolution,[],[f338,f118])).

fof(f338,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl9_14 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl9_14
  <=> r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f379,plain,
    ( spl9_18
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f373,f296,f377])).

fof(f373,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl9_4 ),
    inference(superposition,[],[f127,f350])).

fof(f370,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f255,f287])).

fof(f287,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f286])).

fof(f368,plain,
    ( ~ spl9_17
    | spl9_5 ),
    inference(avatar_split_clause,[],[f364,f301,f366])).

fof(f301,plain,
    ( spl9_5
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f364,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))
    | spl9_5 ),
    inference(forward_demodulation,[],[f302,f129])).

fof(f302,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f301])).

fof(f363,plain,
    ( ~ spl9_16
    | spl9_8 ),
    inference(avatar_split_clause,[],[f359,f313,f361])).

fof(f313,plain,
    ( spl9_8
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f359,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))))
    | spl9_8 ),
    inference(forward_demodulation,[],[f314,f129])).

fof(f314,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3)))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f313])).

fof(f352,plain,
    ( spl9_3
    | spl9_15
    | spl9_13
    | spl9_11
    | spl9_9
    | spl9_7
    | spl9_6
    | spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f220,f289,f296,f304,f308,f316,f324,f332,f340,f293])).

fof(f220,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k1_tarski(sK2)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK0)
    | k1_xboole_0 = sK3
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f109,f209,f130,f130,f130,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f158,f130])).

fof(f158,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f109,plain,
    ( sK3 = k1_enumset1(sK0,sK1,sK2)
    | sK3 = k2_tarski(sK0,sK2)
    | sK3 = k2_tarski(sK1,sK2)
    | sK3 = k2_tarski(sK0,sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK0)
    | k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

% (10050)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
fof(f74,plain,
    ( ( ( sK3 != k1_enumset1(sK0,sK1,sK2)
        & sK3 != k2_tarski(sK0,sK2)
        & sK3 != k2_tarski(sK1,sK2)
        & sK3 != k2_tarski(sK0,sK1)
        & sK3 != k1_tarski(sK2)
        & sK3 != k1_tarski(sK1)
        & sK3 != k1_tarski(sK0)
        & k1_xboole_0 != sK3 )
      | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) )
    & ( sK3 = k1_enumset1(sK0,sK1,sK2)
      | sK3 = k2_tarski(sK0,sK2)
      | sK3 = k2_tarski(sK1,sK2)
      | sK3 = k2_tarski(sK0,sK1)
      | sK3 = k1_tarski(sK2)
      | sK3 = k1_tarski(sK1)
      | sK3 = k1_tarski(sK0)
      | k1_xboole_0 = sK3
      | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f72,f73])).

fof(f73,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k1_enumset1(X0,X1,X2) != X3
            & k2_tarski(X0,X2) != X3
            & k2_tarski(X1,X2) != X3
            & k2_tarski(X0,X1) != X3
            & k1_tarski(X2) != X3
            & k1_tarski(X1) != X3
            & k1_tarski(X0) != X3
            & k1_xboole_0 != X3 )
          | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) )
        & ( k1_enumset1(X0,X1,X2) = X3
          | k2_tarski(X0,X2) = X3
          | k2_tarski(X1,X2) = X3
          | k2_tarski(X0,X1) = X3
          | k1_tarski(X2) = X3
          | k1_tarski(X1) = X3
          | k1_tarski(X0) = X3
          | k1_xboole_0 = X3
          | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) )
   => ( ( ( sK3 != k1_enumset1(sK0,sK1,sK2)
          & sK3 != k2_tarski(sK0,sK2)
          & sK3 != k2_tarski(sK1,sK2)
          & sK3 != k2_tarski(sK0,sK1)
          & sK3 != k1_tarski(sK2)
          & sK3 != k1_tarski(sK1)
          & sK3 != k1_tarski(sK0)
          & k1_xboole_0 != sK3 )
        | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) )
      & ( sK3 = k1_enumset1(sK0,sK1,sK2)
        | sK3 = k2_tarski(sK0,sK2)
        | sK3 = k2_tarski(sK1,sK2)
        | sK3 = k2_tarski(sK0,sK1)
        | sK3 = k1_tarski(sK2)
        | sK3 = k1_tarski(sK1)
        | sK3 = k1_tarski(sK0)
        | k1_xboole_0 = sK3
        | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 )
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 )
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ? [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <~> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      <=> ~ ( k1_enumset1(X0,X1,X2) != X3
            & k2_tarski(X0,X2) != X3
            & k2_tarski(X1,X2) != X3
            & k2_tarski(X0,X1) != X3
            & k1_tarski(X2) != X3
            & k1_tarski(X1) != X3
            & k1_tarski(X0) != X3
            & k1_xboole_0 != X3 ) ) ),
    inference(negated_conjecture,[],[f49])).

fof(f49,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f342,plain,
    ( ~ spl9_14
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f335,f340,f337])).

fof(f335,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(inner_rewriting,[],[f219])).

fof(f219,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f110,f209])).

fof(f110,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f334,plain,
    ( ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f327,f332,f329])).

fof(f327,plain,
    ( sK3 != k1_tarski(sK0)
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(inner_rewriting,[],[f218])).

fof(f218,plain,
    ( sK3 != k1_tarski(sK0)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f111,f209])).

fof(f111,plain,
    ( sK3 != k1_tarski(sK0)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f326,plain,
    ( ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f319,f324,f321])).

fof(f319,plain,
    ( sK3 != k1_tarski(sK1)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2)))) ),
    inference(inner_rewriting,[],[f217])).

fof(f217,plain,
    ( sK3 != k1_tarski(sK1)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f112,f209])).

fof(f112,plain,
    ( sK3 != k1_tarski(sK1)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f318,plain,
    ( ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f311,f316,f313])).

fof(f311,plain,
    ( sK3 != k1_tarski(sK2)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3))) ),
    inference(inner_rewriting,[],[f216])).

fof(f216,plain,
    ( sK3 != k1_tarski(sK2)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f113,f209])).

fof(f113,plain,
    ( sK3 != k1_tarski(sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f310,plain,
    ( ~ spl9_3
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f215,f308,f293])).

fof(f215,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f114,f130,f209])).

fof(f114,plain,
    ( sK3 != k2_tarski(sK0,sK1)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f306,plain,
    ( ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f299,f304,f301])).

fof(f299,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3)) ),
    inference(inner_rewriting,[],[f214])).

fof(f214,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f115,f130,f209])).

fof(f115,plain,
    ( sK3 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f298,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f213,f296,f293])).

fof(f213,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f116,f130,f209])).

fof(f116,plain,
    ( sK3 != k2_tarski(sK0,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

fof(f291,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f284,f289,f286])).

fof(f284,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ r1_tarski(sK3,sK3) ),
    inference(inner_rewriting,[],[f212])).

fof(f212,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f117,f209,f209])).

fof(f117,plain,
    ( sK3 != k1_enumset1(sK0,sK1,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (9776)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (9780)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (9778)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (9775)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (9779)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (9792)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (9784)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (9788)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9777)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9789)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (9783)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (9804)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (9798)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (9790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (9785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (9795)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (9802)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (9803)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (9799)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (9782)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (9791)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (9786)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (9801)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (9787)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9796)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (9800)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (9797)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (9781)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (9794)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (9793)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 3.15/0.80  % (9780)Time limit reached!
% 3.15/0.80  % (9780)------------------------------
% 3.15/0.80  % (9780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.81  % (9780)Termination reason: Time limit
% 3.15/0.81  % (9780)Termination phase: Saturation
% 3.15/0.81  
% 3.15/0.81  % (9780)Memory used [KB]: 9210
% 3.15/0.81  % (9780)Time elapsed: 0.400 s
% 3.15/0.81  % (9780)------------------------------
% 3.15/0.81  % (9780)------------------------------
% 4.03/0.90  % (9785)Time limit reached!
% 4.03/0.90  % (9785)------------------------------
% 4.03/0.90  % (9785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (9776)Time limit reached!
% 4.03/0.91  % (9776)------------------------------
% 4.03/0.91  % (9776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (9787)Time limit reached!
% 4.03/0.91  % (9787)------------------------------
% 4.03/0.91  % (9787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (9787)Termination reason: Time limit
% 4.03/0.91  
% 4.03/0.91  % (9787)Memory used [KB]: 8443
% 4.03/0.91  % (9787)Time elapsed: 0.514 s
% 4.03/0.91  % (9787)------------------------------
% 4.03/0.91  % (9787)------------------------------
% 4.03/0.92  % (9776)Termination reason: Time limit
% 4.03/0.92  % (9776)Termination phase: Saturation
% 4.03/0.92  
% 4.03/0.92  % (9776)Memory used [KB]: 9210
% 4.03/0.92  % (9776)Time elapsed: 0.500 s
% 4.03/0.92  % (9776)------------------------------
% 4.03/0.92  % (9776)------------------------------
% 4.03/0.92  % (9792)Time limit reached!
% 4.03/0.92  % (9792)------------------------------
% 4.03/0.92  % (9792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (9792)Termination reason: Time limit
% 4.03/0.92  
% 4.03/0.92  % (9792)Memory used [KB]: 15223
% 4.03/0.92  % (9792)Time elapsed: 0.519 s
% 4.03/0.92  % (9792)------------------------------
% 4.03/0.92  % (9792)------------------------------
% 4.03/0.93  % (9785)Termination reason: Time limit
% 4.03/0.93  % (9785)Termination phase: Saturation
% 4.03/0.93  
% 4.03/0.93  % (9785)Memory used [KB]: 14200
% 4.03/0.93  % (9785)Time elapsed: 0.500 s
% 4.03/0.93  % (9785)------------------------------
% 4.03/0.93  % (9785)------------------------------
% 4.46/0.93  % (9979)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.46/0.94  % (9775)Time limit reached!
% 4.46/0.94  % (9775)------------------------------
% 4.46/0.94  % (9775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.94  % (9775)Termination reason: Time limit
% 4.46/0.94  % (9775)Termination phase: Saturation
% 4.46/0.94  
% 4.46/0.94  % (9775)Memory used [KB]: 3070
% 4.46/0.94  % (9775)Time elapsed: 0.500 s
% 4.46/0.94  % (9775)------------------------------
% 4.46/0.94  % (9775)------------------------------
% 4.58/1.00  % (9803)Time limit reached!
% 4.58/1.00  % (9803)------------------------------
% 4.58/1.00  % (9803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.00  % (9803)Termination reason: Time limit
% 4.58/1.00  
% 4.58/1.00  % (9803)Memory used [KB]: 7547
% 4.58/1.00  % (9803)Time elapsed: 0.603 s
% 4.58/1.00  % (9803)------------------------------
% 4.58/1.00  % (9803)------------------------------
% 4.58/1.01  % (9782)Time limit reached!
% 4.58/1.01  % (9782)------------------------------
% 4.58/1.01  % (9782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.01  % (10009)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.03/1.02  % (10015)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.03/1.02  % (9782)Termination reason: Time limit
% 5.03/1.02  
% 5.03/1.02  % (9782)Memory used [KB]: 11001
% 5.03/1.02  % (9782)Time elapsed: 0.610 s
% 5.03/1.02  % (9782)------------------------------
% 5.03/1.02  % (9782)------------------------------
% 5.03/1.02  % (10017)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.03/1.03  % (9791)Time limit reached!
% 5.03/1.03  % (9791)------------------------------
% 5.03/1.03  % (9791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.03  % (9791)Termination reason: Time limit
% 5.03/1.03  
% 5.03/1.03  % (9791)Memory used [KB]: 15863
% 5.03/1.03  % (9791)Time elapsed: 0.628 s
% 5.03/1.03  % (9791)------------------------------
% 5.03/1.03  % (9791)------------------------------
% 5.03/1.05  % (10029)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.03/1.05  % (10018)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.61/1.14  % (10040)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.61/1.14  % (10039)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.28/1.16  % (10041)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.50/1.22  % (9796)Time limit reached!
% 6.50/1.22  % (9796)------------------------------
% 6.50/1.22  % (9796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.50/1.22  % (9796)Termination reason: Time limit
% 6.50/1.22  % (9796)Termination phase: Saturation
% 6.50/1.23  
% 6.50/1.23  % (9796)Memory used [KB]: 3454
% 6.50/1.23  % (9796)Time elapsed: 0.800 s
% 6.50/1.23  % (9796)------------------------------
% 6.50/1.23  % (9796)------------------------------
% 7.44/1.35  % (10018)Time limit reached!
% 7.44/1.35  % (10018)------------------------------
% 7.44/1.35  % (10018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.44/1.35  % (10018)Termination reason: Time limit
% 7.44/1.35  
% 7.44/1.35  % (10018)Memory used [KB]: 13944
% 7.44/1.35  % (10018)Time elapsed: 0.405 s
% 7.44/1.35  % (10018)------------------------------
% 7.44/1.35  % (10018)------------------------------
% 7.44/1.36  % (10017)Time limit reached!
% 7.44/1.36  % (10017)------------------------------
% 7.44/1.36  % (10017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.44/1.36  % (10017)Termination reason: Time limit
% 7.44/1.36  
% 7.44/1.36  % (10017)Memory used [KB]: 8443
% 7.44/1.36  % (10017)Time elapsed: 0.418 s
% 7.44/1.36  % (10017)------------------------------
% 7.44/1.36  % (10017)------------------------------
% 7.44/1.36  % (10042)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.93/1.40  % (9777)Time limit reached!
% 7.93/1.40  % (9777)------------------------------
% 7.93/1.40  % (9777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.93/1.42  % (9777)Termination reason: Time limit
% 7.93/1.42  % (9777)Termination phase: Saturation
% 7.93/1.42  
% 7.93/1.42  % (9777)Memory used [KB]: 23794
% 7.93/1.42  % (9777)Time elapsed: 1.0000 s
% 7.93/1.42  % (9777)------------------------------
% 7.93/1.42  % (9777)------------------------------
% 8.57/1.49  % (10043)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.80/1.50  % (10044)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.10/1.53  % (10045)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.14/1.60  % (9797)Time limit reached!
% 9.14/1.60  % (9797)------------------------------
% 9.14/1.60  % (9797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.14/1.60  % (9797)Termination reason: Time limit
% 9.14/1.60  
% 9.14/1.60  % (9797)Memory used [KB]: 17014
% 9.14/1.60  % (9797)Time elapsed: 1.204 s
% 9.14/1.60  % (9797)------------------------------
% 9.14/1.60  % (9797)------------------------------
% 9.94/1.62  % (9801)Time limit reached!
% 9.94/1.62  % (9801)------------------------------
% 9.94/1.62  % (9801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.94/1.64  % (9801)Termination reason: Time limit
% 9.94/1.64  
% 9.94/1.64  % (9801)Memory used [KB]: 15095
% 9.94/1.64  % (9801)Time elapsed: 1.221 s
% 9.94/1.64  % (9801)------------------------------
% 9.94/1.64  % (9801)------------------------------
% 10.41/1.71  % (9799)Time limit reached!
% 10.41/1.71  % (9799)------------------------------
% 10.41/1.71  % (9799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.41/1.72  % (9799)Termination reason: Time limit
% 10.41/1.72  
% 10.41/1.72  % (9799)Memory used [KB]: 17654
% 10.41/1.72  % (9799)Time elapsed: 1.311 s
% 10.41/1.72  % (9799)------------------------------
% 10.41/1.72  % (9799)------------------------------
% 10.41/1.74  % (9790)Time limit reached!
% 10.41/1.74  % (9790)------------------------------
% 10.41/1.74  % (9790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.41/1.75  % (10046)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 10.41/1.75  % (9790)Termination reason: Time limit
% 10.41/1.75  
% 10.41/1.75  % (9790)Memory used [KB]: 18805
% 10.41/1.75  % (9790)Time elapsed: 1.307 s
% 10.41/1.75  % (9790)------------------------------
% 10.41/1.75  % (9790)------------------------------
% 11.11/1.77  % (10047)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.51/1.86  % (10048)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.51/1.89  % (10049)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.09/1.91  % (9802)Time limit reached!
% 12.09/1.91  % (9802)------------------------------
% 12.09/1.91  % (9802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.09/1.92  % (9779)Time limit reached!
% 12.09/1.92  % (9779)------------------------------
% 12.09/1.92  % (9779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.09/1.93  % (9779)Termination reason: Time limit
% 12.09/1.93  
% 12.09/1.93  % (9779)Memory used [KB]: 13048
% 12.09/1.93  % (9779)Time elapsed: 1.520 s
% 12.09/1.93  % (9779)------------------------------
% 12.09/1.93  % (9779)------------------------------
% 12.09/1.93  % (9802)Termination reason: Time limit
% 12.09/1.93  % (9802)Termination phase: Saturation
% 12.09/1.93  
% 12.09/1.93  % (9802)Memory used [KB]: 15479
% 12.09/1.93  % (9802)Time elapsed: 1.500 s
% 12.09/1.93  % (9802)------------------------------
% 12.09/1.93  % (9802)------------------------------
% 12.09/1.97  % (10045)Time limit reached!
% 12.09/1.97  % (10045)------------------------------
% 12.09/1.97  % (10045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.09/1.97  % (10045)Termination reason: Time limit
% 12.09/1.97  
% 12.09/1.97  % (10045)Memory used [KB]: 3837
% 12.09/1.97  % (10045)Time elapsed: 0.510 s
% 12.09/1.97  % (10045)------------------------------
% 12.09/1.97  % (10045)------------------------------
% 12.62/2.01  % (9786)Time limit reached!
% 12.62/2.01  % (9786)------------------------------
% 12.62/2.01  % (9786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.62/2.03  % (9794)Refutation found. Thanks to Tanya!
% 12.62/2.03  % SZS status Theorem for theBenchmark
% 12.62/2.04  % (9786)Termination reason: Time limit
% 12.62/2.04  
% 12.62/2.04  % (9786)Memory used [KB]: 25458
% 12.62/2.04  % (9786)Time elapsed: 1.616 s
% 12.62/2.04  % (9786)------------------------------
% 12.62/2.04  % (9786)------------------------------
% 12.62/2.04  % SZS output start Proof for theBenchmark
% 12.62/2.04  fof(f25396,plain,(
% 12.62/2.04    $false),
% 12.62/2.04    inference(avatar_sat_refutation,[],[f291,f298,f306,f310,f318,f326,f334,f342,f352,f363,f368,f370,f379,f496,f503,f510,f519,f589,f2143,f6320,f6353,f6354,f6445,f6455,f6589,f6714,f6722,f6736,f6749,f7179,f7192,f7198,f7204,f7483,f7489,f7605,f7643,f7685,f7883,f7909,f9194,f9733,f9981,f9987,f9992,f10037,f10855,f10874,f10883,f10910,f10981,f10991,f11035,f11349,f11355,f11434,f11571,f11653,f11675,f11681,f12099,f12214,f12758,f12780,f12781,f13259,f13680,f13965,f13972,f14052,f14087,f14128,f14131,f14677,f14682,f14700,f14705,f15514,f18616,f18646,f19054,f19118,f19171,f19201,f19210,f20146,f20154,f20269,f20294,f20376,f20802,f20816,f20927,f20931,f21088,f21223,f21333,f21522,f21561,f21582,f22414,f22633,f22689,f24389,f24451,f24653,f24725,f25068,f25385])).
% 12.62/2.05  % (10051)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.62/2.05  fof(f25385,plain,(
% 12.62/2.05    spl9_6 | spl9_15 | spl9_11 | spl9_9 | ~spl9_77),
% 12.62/2.05    inference(avatar_split_clause,[],[f25376,f7575,f316,f324,f340,f304])).
% 12.62/2.05  fof(f304,plain,(
% 12.62/2.05    spl9_6 <=> sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 12.62/2.05  fof(f340,plain,(
% 12.62/2.05    spl9_15 <=> k1_xboole_0 = sK3),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 12.62/2.05  fof(f324,plain,(
% 12.62/2.05    spl9_11 <=> sK3 = k1_tarski(sK1)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 12.62/2.05  fof(f316,plain,(
% 12.62/2.05    spl9_9 <=> sK3 = k1_tarski(sK2)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 12.62/2.05  fof(f7575,plain,(
% 12.62/2.05    spl9_77 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).
% 12.62/2.05  fof(f25376,plain,(
% 12.62/2.05    sK3 = k1_tarski(sK2) | sK3 = k1_tarski(sK1) | k1_xboole_0 = sK3 | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~spl9_77),
% 12.62/2.05    inference(resolution,[],[f25239,f241])).
% 12.62/2.05  fof(f241,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0) )),
% 12.62/2.05    inference(definition_unfolding,[],[f182,f130,f130])).
% 12.62/2.05  fof(f130,plain,(
% 12.62/2.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f30])).
% 12.62/2.05  fof(f30,axiom,(
% 12.62/2.05    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 12.62/2.05  fof(f182,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f102])).
% 12.62/2.05  fof(f102,plain,(
% 12.62/2.05    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 12.62/2.05    inference(flattening,[],[f101])).
% 12.62/2.05  fof(f101,plain,(
% 12.62/2.05    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 12.62/2.05    inference(nnf_transformation,[],[f67])).
% 12.62/2.05  fof(f67,plain,(
% 12.62/2.05    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 12.62/2.05    inference(ennf_transformation,[],[f41])).
% 12.62/2.05  fof(f41,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 12.62/2.05  fof(f25239,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~spl9_77),
% 12.62/2.05    inference(avatar_component_clause,[],[f7575])).
% 12.62/2.05  fof(f25068,plain,(
% 12.62/2.05    spl9_100 | ~spl9_99),
% 12.62/2.05    inference(avatar_split_clause,[],[f25067,f7818,f7821])).
% 12.62/2.05  fof(f7821,plain,(
% 12.62/2.05    spl9_100 <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK0))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).
% 12.62/2.05  fof(f7818,plain,(
% 12.62/2.05    spl9_99 <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).
% 12.62/2.05  fof(f25067,plain,(
% 12.62/2.05    sK3 = k4_xboole_0(sK3,k1_tarski(sK0)) | ~spl9_99),
% 12.62/2.05    inference(forward_demodulation,[],[f25066,f121])).
% 12.62/2.05  fof(f121,plain,(
% 12.62/2.05    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.62/2.05    inference(cnf_transformation,[],[f9])).
% 12.62/2.05  fof(f9,axiom,(
% 12.62/2.05    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 12.62/2.05  fof(f25066,plain,(
% 12.62/2.05    k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK0)) | ~spl9_99),
% 12.62/2.05    inference(forward_demodulation,[],[f25065,f394])).
% 12.62/2.05  fof(f394,plain,(
% 12.62/2.05    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 12.62/2.05    inference(superposition,[],[f127,f129])).
% 12.62/2.05  fof(f129,plain,(
% 12.62/2.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.62/2.05    inference(cnf_transformation,[],[f1])).
% 12.62/2.05  fof(f1,axiom,(
% 12.62/2.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 12.62/2.05  fof(f127,plain,(
% 12.62/2.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f21])).
% 12.62/2.05  fof(f21,axiom,(
% 12.62/2.05    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 12.62/2.05  fof(f25065,plain,(
% 12.62/2.05    k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),sK3))) | ~spl9_99),
% 12.62/2.05    inference(forward_demodulation,[],[f25057,f160])).
% 12.62/2.05  fof(f160,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f16])).
% 12.62/2.05  fof(f16,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 12.62/2.05  fof(f25057,plain,(
% 12.62/2.05    k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),sK3)) | ~spl9_99),
% 12.62/2.05    inference(resolution,[],[f20042,f135])).
% 12.62/2.05  fof(f135,plain,(
% 12.62/2.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 12.62/2.05    inference(cnf_transformation,[],[f57])).
% 12.62/2.05  fof(f57,plain,(
% 12.62/2.05    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 12.62/2.05    inference(ennf_transformation,[],[f20])).
% 12.62/2.05  fof(f20,axiom,(
% 12.62/2.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 12.62/2.05  fof(f20042,plain,(
% 12.62/2.05    r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0))) | ~spl9_99),
% 12.62/2.05    inference(avatar_component_clause,[],[f7818])).
% 12.62/2.05  fof(f24725,plain,(
% 12.62/2.05    ~spl9_19 | spl9_24 | ~spl9_25),
% 12.62/2.05    inference(avatar_split_clause,[],[f24724,f445,f437,f385])).
% 12.62/2.05  fof(f385,plain,(
% 12.62/2.05    spl9_19 <=> sK3 = k2_xboole_0(k1_tarski(sK0),sK3)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 12.62/2.05  fof(f437,plain,(
% 12.62/2.05    spl9_24 <=> sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 12.62/2.05  fof(f445,plain,(
% 12.62/2.05    spl9_25 <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK1))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 12.62/2.05  fof(f24724,plain,(
% 12.62/2.05    sK3 != k2_xboole_0(k1_tarski(sK0),sK3) | (spl9_24 | ~spl9_25)),
% 12.62/2.05    inference(forward_demodulation,[],[f438,f6603])).
% 12.62/2.05  fof(f6603,plain,(
% 12.62/2.05    sK3 = k2_xboole_0(sK3,k1_tarski(sK1)) | ~spl9_25),
% 12.62/2.05    inference(avatar_component_clause,[],[f445])).
% 12.62/2.05  fof(f438,plain,(
% 12.62/2.05    sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))) | spl9_24),
% 12.62/2.05    inference(avatar_component_clause,[],[f437])).
% 12.62/2.05  fof(f24653,plain,(
% 12.62/2.05    spl9_22 | ~spl9_1 | spl9_376),
% 12.62/2.05    inference(avatar_split_clause,[],[f22191,f22141,f286,f419])).
% 12.62/2.05  fof(f419,plain,(
% 12.62/2.05    spl9_22 <=> r2_hidden(sK2,sK3)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 12.62/2.05  fof(f286,plain,(
% 12.62/2.05    spl9_1 <=> r1_tarski(sK3,sK3)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 12.62/2.05  fof(f22141,plain,(
% 12.62/2.05    spl9_376 <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_376])])).
% 12.62/2.05  fof(f22191,plain,(
% 12.62/2.05    ~r1_tarski(sK3,sK3) | r2_hidden(sK2,sK3) | spl9_376),
% 12.62/2.05    inference(superposition,[],[f22142,f152])).
% 12.62/2.05  fof(f152,plain,(
% 12.62/2.05    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 12.62/2.05    inference(cnf_transformation,[],[f87])).
% 12.62/2.05  fof(f87,plain,(
% 12.62/2.05    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 12.62/2.05    inference(nnf_transformation,[],[f46])).
% 12.62/2.05  fof(f46,axiom,(
% 12.62/2.05    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 12.62/2.05  fof(f22142,plain,(
% 12.62/2.05    ~r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2))) | spl9_376),
% 12.62/2.05    inference(avatar_component_clause,[],[f22141])).
% 12.62/2.05  fof(f24451,plain,(
% 12.62/2.05    spl9_207 | ~spl9_3 | ~spl9_65 | ~spl9_66 | ~spl9_377),
% 12.62/2.05    inference(avatar_split_clause,[],[f24449,f22144,f7202,f7196,f293,f12097])).
% 12.62/2.05  fof(f12097,plain,(
% 12.62/2.05    spl9_207 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).
% 12.62/2.05  fof(f293,plain,(
% 12.62/2.05    spl9_3 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 12.62/2.05  fof(f7196,plain,(
% 12.62/2.05    spl9_65 <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 12.62/2.05  fof(f7202,plain,(
% 12.62/2.05    spl9_66 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 12.62/2.05  fof(f22144,plain,(
% 12.62/2.05    spl9_377 <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK2))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).
% 12.62/2.05  fof(f24449,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl9_3 | ~spl9_65 | ~spl9_66 | ~spl9_377)),
% 12.62/2.05    inference(forward_demodulation,[],[f24448,f392])).
% 12.62/2.05  fof(f392,plain,(
% 12.62/2.05    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 12.62/2.05    inference(superposition,[],[f129,f121])).
% 12.62/2.05  fof(f24448,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) | (~spl9_3 | ~spl9_65 | ~spl9_66 | ~spl9_377)),
% 12.62/2.05    inference(forward_demodulation,[],[f24447,f8403])).
% 12.62/2.05  fof(f8403,plain,(
% 12.62/2.05    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X9))) )),
% 12.62/2.05    inference(superposition,[],[f159,f129])).
% 12.62/2.05  fof(f159,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f24])).
% 12.62/2.05  fof(f24,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 12.62/2.05  fof(f24447,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_xboole_0))) | (~spl9_3 | ~spl9_65 | ~spl9_66 | ~spl9_377)),
% 12.62/2.05    inference(forward_demodulation,[],[f24446,f374])).
% 12.62/2.05  fof(f374,plain,(
% 12.62/2.05    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 12.62/2.05    inference(superposition,[],[f127,f121])).
% 12.62/2.05  fof(f24446,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2))))) | (~spl9_3 | ~spl9_65 | ~spl9_66 | ~spl9_377)),
% 12.62/2.05    inference(forward_demodulation,[],[f24445,f12611])).
% 12.62/2.05  fof(f12611,plain,(
% 12.62/2.05    ( ! [X1] : (k4_xboole_0(k2_xboole_0(k1_tarski(sK1),X1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(X1,k1_tarski(sK2)))) ) | ~spl9_65),
% 12.62/2.05    inference(superposition,[],[f163,f7197])).
% 12.62/2.05  fof(f7197,plain,(
% 12.62/2.05    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~spl9_65),
% 12.62/2.05    inference(avatar_component_clause,[],[f7196])).
% 12.62/2.05  fof(f163,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f17])).
% 12.62/2.05  fof(f17,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 12.62/2.05  fof(f24445,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK2)))) | (~spl9_3 | ~spl9_66 | ~spl9_377)),
% 12.62/2.05    inference(forward_demodulation,[],[f24411,f23825])).
% 12.62/2.05  fof(f23825,plain,(
% 12.62/2.05    ( ! [X2] : (k2_xboole_0(k1_tarski(sK0),k4_xboole_0(X2,k1_tarski(sK2))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X2),k1_tarski(sK2))) ) | ~spl9_66),
% 12.62/2.05    inference(superposition,[],[f163,f7203])).
% 12.62/2.05  fof(f7203,plain,(
% 12.62/2.05    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | ~spl9_66),
% 12.62/2.05    inference(avatar_component_clause,[],[f7202])).
% 12.62/2.05  fof(f24411,plain,(
% 12.62/2.05    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK2))) | (~spl9_3 | ~spl9_377)),
% 12.62/2.05    inference(superposition,[],[f14312,f22145])).
% 12.62/2.05  fof(f22145,plain,(
% 12.62/2.05    sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_377),
% 12.62/2.05    inference(avatar_component_clause,[],[f22144])).
% 12.62/2.05  fof(f14312,plain,(
% 12.62/2.05    ( ! [X1] : (r1_tarski(k4_xboole_0(sK3,X1),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),X1))) ) | ~spl9_3),
% 12.62/2.05    inference(resolution,[],[f343,f166])).
% 12.62/2.05  fof(f166,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 12.62/2.05    inference(cnf_transformation,[],[f63])).
% 12.62/2.05  fof(f63,plain,(
% 12.62/2.05    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 12.62/2.05    inference(ennf_transformation,[],[f13])).
% 12.62/2.05  fof(f13,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 12.62/2.05  fof(f343,plain,(
% 12.62/2.05    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | ~spl9_3),
% 12.62/2.05    inference(avatar_component_clause,[],[f293])).
% 12.62/2.05  fof(f24389,plain,(
% 12.62/2.05    spl9_377 | ~spl9_376),
% 12.62/2.05    inference(avatar_split_clause,[],[f24388,f22141,f22144])).
% 12.62/2.05  fof(f24388,plain,(
% 12.62/2.05    sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_376),
% 12.62/2.05    inference(forward_demodulation,[],[f24387,f121])).
% 12.62/2.05  fof(f24387,plain,(
% 12.62/2.05    k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_376),
% 12.62/2.05    inference(forward_demodulation,[],[f24386,f394])).
% 12.62/2.05  fof(f24386,plain,(
% 12.62/2.05    k4_xboole_0(sK3,k1_tarski(sK2)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),sK3))) | ~spl9_376),
% 12.62/2.05    inference(forward_demodulation,[],[f24378,f160])).
% 12.62/2.05  fof(f24378,plain,(
% 12.62/2.05    k4_xboole_0(sK3,k1_tarski(sK2)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),sK3)) | ~spl9_376),
% 12.62/2.05    inference(resolution,[],[f24364,f135])).
% 12.62/2.05  fof(f24364,plain,(
% 12.62/2.05    r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK2))) | ~spl9_376),
% 12.62/2.05    inference(avatar_component_clause,[],[f22141])).
% 12.62/2.05  fof(f22689,plain,(
% 12.62/2.05    ~spl9_22 | spl9_111),
% 12.62/2.05    inference(avatar_split_clause,[],[f17359,f8261,f419])).
% 12.62/2.05  fof(f8261,plain,(
% 12.62/2.05    spl9_111 <=> r1_tarski(k1_tarski(sK2),sK3)),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).
% 12.62/2.05  fof(f17359,plain,(
% 12.62/2.05    ~r2_hidden(sK2,sK3) | spl9_111),
% 12.62/2.05    inference(resolution,[],[f10824,f16590])).
% 12.62/2.05  fof(f16590,plain,(
% 12.62/2.05    ~r1_tarski(k1_tarski(sK2),sK3) | spl9_111),
% 12.62/2.05    inference(avatar_component_clause,[],[f8261])).
% 12.62/2.05  fof(f10824,plain,(
% 12.62/2.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 12.62/2.05    inference(duplicate_literal_removal,[],[f10816])).
% 12.62/2.05  fof(f10816,plain,(
% 12.62/2.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 12.62/2.05    inference(superposition,[],[f247,f211])).
% 12.62/2.05  fof(f211,plain,(
% 12.62/2.05    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 12.62/2.05    inference(definition_unfolding,[],[f123,f130])).
% 12.62/2.05  fof(f123,plain,(
% 12.62/2.05    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 12.62/2.05    inference(cnf_transformation,[],[f33])).
% 12.62/2.05  fof(f33,axiom,(
% 12.62/2.05    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 12.62/2.05  fof(f247,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 12.62/2.05    inference(definition_unfolding,[],[f194,f130])).
% 12.62/2.05  fof(f194,plain,(
% 12.62/2.05    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 12.62/2.05    inference(cnf_transformation,[],[f106])).
% 12.62/2.05  fof(f106,plain,(
% 12.62/2.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 12.62/2.05    inference(flattening,[],[f105])).
% 12.62/2.05  fof(f105,plain,(
% 12.62/2.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 12.62/2.05    inference(nnf_transformation,[],[f40])).
% 12.62/2.05  fof(f40,axiom,(
% 12.62/2.05    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 12.62/2.05  fof(f22633,plain,(
% 12.62/2.05    spl9_2 | ~spl9_21 | ~spl9_25 | ~spl9_36 | ~spl9_43),
% 12.62/2.05    inference(avatar_split_clause,[],[f22632,f6408,f6318,f445,f401,f289])).
% 12.62/2.05  fof(f289,plain,(
% 12.62/2.05    spl9_2 <=> sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 12.62/2.05  fof(f401,plain,(
% 12.62/2.05    spl9_21 <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK0))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 12.62/2.05  fof(f6318,plain,(
% 12.62/2.05    spl9_36 <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 12.62/2.05  fof(f6408,plain,(
% 12.62/2.05    spl9_43 <=> sK3 = k2_xboole_0(sK3,k1_tarski(sK2))),
% 12.62/2.05    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 12.62/2.05  fof(f22632,plain,(
% 12.62/2.05    sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | (~spl9_21 | ~spl9_25 | ~spl9_36 | ~spl9_43)),
% 12.62/2.05    inference(forward_demodulation,[],[f22631,f11147])).
% 12.62/2.05  fof(f11147,plain,(
% 12.62/2.05    sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_43),
% 12.62/2.05    inference(avatar_component_clause,[],[f6408])).
% 12.62/2.05  fof(f22631,plain,(
% 12.62/2.05    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k1_tarski(sK2)) | (~spl9_21 | ~spl9_25 | ~spl9_36)),
% 12.62/2.05    inference(forward_demodulation,[],[f22630,f21911])).
% 12.62/2.05  fof(f21911,plain,(
% 12.62/2.05    ( ! [X2] : (k2_xboole_0(sK3,X2) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),X2))) ) | ~spl9_25),
% 12.62/2.05    inference(superposition,[],[f159,f6603])).
% 12.62/2.05  fof(f22630,plain,(
% 12.62/2.05    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | (~spl9_21 | ~spl9_36)),
% 12.62/2.05    inference(forward_demodulation,[],[f22586,f21931])).
% 12.62/2.05  fof(f21931,plain,(
% 12.62/2.05    ( ! [X2] : (k2_xboole_0(sK3,X2) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),X2))) ) | ~spl9_21),
% 12.62/2.05    inference(superposition,[],[f159,f6718])).
% 12.62/2.05  fof(f6718,plain,(
% 12.62/2.05    sK3 = k2_xboole_0(sK3,k1_tarski(sK0)) | ~spl9_21),
% 12.62/2.05    inference(avatar_component_clause,[],[f401])).
% 12.62/2.05  fof(f22586,plain,(
% 12.62/2.05    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | ~spl9_36),
% 12.62/2.05    inference(superposition,[],[f8388,f6319])).
% 12.62/2.05  fof(f6319,plain,(
% 12.62/2.05    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)) | ~spl9_36),
% 12.62/2.05    inference(avatar_component_clause,[],[f6318])).
% 12.62/2.05  fof(f8388,plain,(
% 12.62/2.05    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 12.62/2.05    inference(superposition,[],[f159,f126])).
% 12.62/2.05  fof(f126,plain,(
% 12.62/2.05    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.62/2.05    inference(cnf_transformation,[],[f51])).
% 12.62/2.05  fof(f51,plain,(
% 12.62/2.05    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.62/2.05    inference(rectify,[],[f4])).
% 12.62/2.05  fof(f4,axiom,(
% 12.62/2.05    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.62/2.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 12.62/2.05  fof(f22414,plain,(
% 12.62/2.05    spl9_207 | ~spl9_354),
% 12.62/2.05    inference(avatar_contradiction_clause,[],[f22413])).
% 12.62/2.06  fof(f22413,plain,(
% 12.62/2.06    $false | (spl9_207 | ~spl9_354)),
% 12.62/2.06    inference(subsumption_resolution,[],[f21332,f22411])).
% 12.62/2.06  fof(f22411,plain,(
% 12.62/2.06    ( ! [X0] : (~r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)))) ) | spl9_207),
% 12.62/2.06    inference(resolution,[],[f12098,f230])).
% 12.62/2.06  fof(f230,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 12.62/2.06    inference(definition_unfolding,[],[f167,f131])).
% 12.62/2.06  fof(f131,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f22])).
% 12.62/2.06  fof(f22,axiom,(
% 12.62/2.06    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 12.62/2.06  fof(f167,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 12.62/2.06    inference(cnf_transformation,[],[f64])).
% 12.62/2.06  fof(f64,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 12.62/2.06    inference(ennf_transformation,[],[f8])).
% 12.62/2.06  fof(f8,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 12.62/2.06  fof(f12098,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl9_207),
% 12.62/2.06    inference(avatar_component_clause,[],[f12097])).
% 12.62/2.06  fof(f21332,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3))) | ~spl9_354),
% 12.62/2.06    inference(avatar_component_clause,[],[f21331])).
% 12.62/2.06  fof(f21331,plain,(
% 12.62/2.06    spl9_354 <=> r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).
% 12.62/2.06  fof(f21582,plain,(
% 12.62/2.06    ~spl9_64 | ~spl9_81),
% 12.62/2.06    inference(avatar_split_clause,[],[f7741,f7603,f7190])).
% 12.62/2.06  fof(f7190,plain,(
% 12.62/2.06    spl9_64 <=> r2_hidden(sK0,k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 12.62/2.06  fof(f7603,plain,(
% 12.62/2.06    spl9_81 <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).
% 12.62/2.06  fof(f7741,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k1_tarski(sK2)) | ~spl9_81),
% 12.62/2.06    inference(superposition,[],[f831,f7604])).
% 12.62/2.06  fof(f7604,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) | ~spl9_81),
% 12.62/2.06    inference(avatar_component_clause,[],[f7603])).
% 12.62/2.06  fof(f831,plain,(
% 12.62/2.06    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0)))) )),
% 12.62/2.06    inference(resolution,[],[f266,f258])).
% 12.62/2.06  fof(f258,plain,(
% 12.62/2.06    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 12.62/2.06    inference(equality_resolution,[],[f257])).
% 12.62/2.06  fof(f257,plain,(
% 12.62/2.06    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 12.62/2.06    inference(equality_resolution,[],[f144])).
% 12.62/2.06  fof(f144,plain,(
% 12.62/2.06    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 12.62/2.06    inference(cnf_transformation,[],[f84])).
% 12.62/2.06  fof(f84,plain,(
% 12.62/2.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 12.62/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f82,f83])).
% 12.62/2.06  fof(f83,plain,(
% 12.62/2.06    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 12.62/2.06    introduced(choice_axiom,[])).
% 12.62/2.06  fof(f82,plain,(
% 12.62/2.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 12.62/2.06    inference(rectify,[],[f81])).
% 12.62/2.06  fof(f81,plain,(
% 12.62/2.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 12.62/2.06    inference(nnf_transformation,[],[f27])).
% 12.62/2.06  fof(f27,axiom,(
% 12.62/2.06    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 12.62/2.06  fof(f266,plain,(
% 12.62/2.06    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.62/2.06    inference(equality_resolution,[],[f177])).
% 12.62/2.06  fof(f177,plain,(
% 12.62/2.06    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.62/2.06    inference(cnf_transformation,[],[f100])).
% 12.62/2.06  fof(f100,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.62/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f98,f99])).
% 12.62/2.06  fof(f99,plain,(
% 12.62/2.06    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((~r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 12.62/2.06    introduced(choice_axiom,[])).
% 12.62/2.06  fof(f98,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.62/2.06    inference(rectify,[],[f97])).
% 12.62/2.06  fof(f97,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.62/2.06    inference(flattening,[],[f96])).
% 12.62/2.06  fof(f96,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.62/2.06    inference(nnf_transformation,[],[f3])).
% 12.62/2.06  fof(f3,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 12.62/2.06  fof(f21561,plain,(
% 12.62/2.06    ~spl9_91 | spl9_84),
% 12.62/2.06    inference(avatar_split_clause,[],[f14306,f7638,f7700])).
% 12.62/2.06  fof(f7700,plain,(
% 12.62/2.06    spl9_91 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 12.62/2.06  fof(f7638,plain,(
% 12.62/2.06    spl9_84 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).
% 12.62/2.06  fof(f14306,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) | spl9_84),
% 12.62/2.06    inference(forward_demodulation,[],[f14304,f223])).
% 12.62/2.06  fof(f223,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 12.62/2.06    inference(definition_unfolding,[],[f128,f130,f130])).
% 12.62/2.06  fof(f128,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f26])).
% 12.62/2.06  fof(f26,axiom,(
% 12.62/2.06    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 12.62/2.06  fof(f14304,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))) | spl9_84),
% 12.62/2.06    inference(resolution,[],[f7639,f168])).
% 12.62/2.06  fof(f168,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.62/2.06    inference(cnf_transformation,[],[f65])).
% 12.62/2.06  fof(f65,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.62/2.06    inference(ennf_transformation,[],[f18])).
% 12.62/2.06  fof(f18,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.62/2.06  fof(f7639,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0)) | spl9_84),
% 12.62/2.06    inference(avatar_component_clause,[],[f7638])).
% 12.62/2.06  fof(f21522,plain,(
% 12.62/2.06    spl9_43 | ~spl9_32),
% 12.62/2.06    inference(avatar_split_clause,[],[f11807,f2141,f6408])).
% 12.62/2.06  fof(f2141,plain,(
% 12.62/2.06    spl9_32 <=> sK3 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 12.62/2.06  fof(f11807,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_32),
% 12.62/2.06    inference(superposition,[],[f129,f2142])).
% 12.62/2.06  fof(f2142,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK2),sK3) | ~spl9_32),
% 12.62/2.06    inference(avatar_component_clause,[],[f2141])).
% 12.62/2.06  fof(f21333,plain,(
% 12.62/2.06    spl9_354 | ~spl9_197 | ~spl9_336),
% 12.62/2.06    inference(avatar_split_clause,[],[f21329,f20798,f11347,f21331])).
% 12.62/2.06  fof(f11347,plain,(
% 12.62/2.06    spl9_197 <=> sK0 = sK2),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_197])])).
% 12.62/2.06  fof(f20798,plain,(
% 12.62/2.06    spl9_336 <=> r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_336])])).
% 12.62/2.06  fof(f21329,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3))) | (~spl9_197 | ~spl9_336)),
% 12.62/2.06    inference(forward_demodulation,[],[f21328,f223])).
% 12.62/2.06  fof(f21328,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),sK3))) | (~spl9_197 | ~spl9_336)),
% 12.62/2.06    inference(forward_demodulation,[],[f21327,f2135])).
% 12.62/2.06  fof(f2135,plain,(
% 12.62/2.06    ( ! [X2,X1] : (k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X1)))) )),
% 12.62/2.06    inference(resolution,[],[f134,f261])).
% 12.62/2.06  fof(f261,plain,(
% 12.62/2.06    ( ! [X4,X0] : (r2_hidden(X4,k2_xboole_0(k1_tarski(X0),k1_tarski(X4)))) )),
% 12.62/2.06    inference(equality_resolution,[],[f260])).
% 12.62/2.06  fof(f260,plain,(
% 12.62/2.06    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_xboole_0(k1_tarski(X0),k1_tarski(X4)) != X2) )),
% 12.62/2.06    inference(equality_resolution,[],[f234])).
% 12.62/2.06  fof(f234,plain,(
% 12.62/2.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2) )),
% 12.62/2.06    inference(definition_unfolding,[],[f172,f130])).
% 12.62/2.06  fof(f172,plain,(
% 12.62/2.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 12.62/2.06    inference(cnf_transformation,[],[f95])).
% 12.62/2.06  fof(f95,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 12.62/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f93,f94])).
% 12.62/2.06  fof(f94,plain,(
% 12.62/2.06    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 12.62/2.06    introduced(choice_axiom,[])).
% 12.62/2.06  fof(f93,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 12.62/2.06    inference(rectify,[],[f92])).
% 12.62/2.06  fof(f92,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 12.62/2.06    inference(flattening,[],[f91])).
% 12.62/2.06  fof(f91,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 12.62/2.06    inference(nnf_transformation,[],[f28])).
% 12.62/2.06  fof(f28,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 12.62/2.06  fof(f134,plain,(
% 12.62/2.06    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 12.62/2.06    inference(cnf_transformation,[],[f56])).
% 12.62/2.06  fof(f56,plain,(
% 12.62/2.06    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 12.62/2.06    inference(ennf_transformation,[],[f43])).
% 12.62/2.06  fof(f43,axiom,(
% 12.62/2.06    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 12.62/2.06  fof(f21327,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),sK3))) | (~spl9_197 | ~spl9_336)),
% 12.62/2.06    inference(forward_demodulation,[],[f20799,f11348])).
% 12.62/2.06  fof(f11348,plain,(
% 12.62/2.06    sK0 = sK2 | ~spl9_197),
% 12.62/2.06    inference(avatar_component_clause,[],[f11347])).
% 12.62/2.06  fof(f20799,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))) | ~spl9_336),
% 12.62/2.06    inference(avatar_component_clause,[],[f20798])).
% 12.62/2.06  fof(f21223,plain,(
% 12.62/2.06    spl9_18 | ~spl9_19),
% 12.62/2.06    inference(avatar_split_clause,[],[f6941,f385,f377])).
% 12.62/2.06  fof(f377,plain,(
% 12.62/2.06    spl9_18 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 12.62/2.06  fof(f6941,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3) | ~spl9_19),
% 12.62/2.06    inference(superposition,[],[f127,f6719])).
% 12.62/2.06  fof(f6719,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),sK3) | ~spl9_19),
% 12.62/2.06    inference(avatar_component_clause,[],[f385])).
% 12.62/2.06  fof(f21088,plain,(
% 12.62/2.06    spl9_35 | ~spl9_38),
% 12.62/2.06    inference(avatar_split_clause,[],[f6741,f6345,f3386])).
% 12.62/2.06  fof(f3386,plain,(
% 12.62/2.06    spl9_35 <=> r2_hidden(sK1,sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 12.62/2.06  fof(f6345,plain,(
% 12.62/2.06    spl9_38 <=> r1_tarski(k1_tarski(sK1),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 12.62/2.06  fof(f6741,plain,(
% 12.62/2.06    r2_hidden(sK1,sK3) | ~spl9_38),
% 12.62/2.06    inference(resolution,[],[f6346,f2961])).
% 12.62/2.06  fof(f2961,plain,(
% 12.62/2.06    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 12.62/2.06    inference(resolution,[],[f140,f258])).
% 12.62/2.06  fof(f140,plain,(
% 12.62/2.06    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f80])).
% 12.62/2.06  fof(f80,plain,(
% 12.62/2.06    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.62/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f78,f79])).
% 12.62/2.06  fof(f79,plain,(
% 12.62/2.06    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 12.62/2.06    introduced(choice_axiom,[])).
% 12.62/2.06  fof(f78,plain,(
% 12.62/2.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.62/2.06    inference(rectify,[],[f77])).
% 12.62/2.06  fof(f77,plain,(
% 12.62/2.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.62/2.06    inference(nnf_transformation,[],[f59])).
% 12.62/2.06  fof(f59,plain,(
% 12.62/2.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.62/2.06    inference(ennf_transformation,[],[f2])).
% 12.62/2.06  fof(f2,axiom,(
% 12.62/2.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 12.62/2.06  fof(f6346,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK1),sK3) | ~spl9_38),
% 12.62/2.06    inference(avatar_component_clause,[],[f6345])).
% 12.62/2.06  fof(f20931,plain,(
% 12.62/2.06    spl9_39 | ~spl9_1 | spl9_99),
% 12.62/2.06    inference(avatar_split_clause,[],[f7826,f7818,f286,f6349])).
% 12.62/2.06  fof(f6349,plain,(
% 12.62/2.06    spl9_39 <=> r2_hidden(sK0,sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 12.62/2.06  fof(f7826,plain,(
% 12.62/2.06    ~r1_tarski(sK3,sK3) | r2_hidden(sK0,sK3) | spl9_99),
% 12.62/2.06    inference(superposition,[],[f7819,f152])).
% 12.62/2.06  fof(f7819,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK0))) | spl9_99),
% 12.62/2.06    inference(avatar_component_clause,[],[f7818])).
% 12.62/2.06  fof(f20927,plain,(
% 12.62/2.06    spl9_35 | ~spl9_1 | spl9_105),
% 12.62/2.06    inference(avatar_split_clause,[],[f7919,f7911,f286,f3386])).
% 12.62/2.06  fof(f7911,plain,(
% 12.62/2.06    spl9_105 <=> r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).
% 12.62/2.06  fof(f7919,plain,(
% 12.62/2.06    ~r1_tarski(sK3,sK3) | r2_hidden(sK1,sK3) | spl9_105),
% 12.62/2.06    inference(superposition,[],[f7912,f152])).
% 12.62/2.06  fof(f7912,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1))) | spl9_105),
% 12.62/2.06    inference(avatar_component_clause,[],[f7911])).
% 12.62/2.06  fof(f20816,plain,(
% 12.62/2.06    ~spl9_207 | spl9_235),
% 12.62/2.06    inference(avatar_split_clause,[],[f14288,f14050,f12097])).
% 12.62/2.06  fof(f14050,plain,(
% 12.62/2.06    spl9_235 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).
% 12.62/2.06  fof(f14288,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl9_235),
% 12.62/2.06    inference(forward_demodulation,[],[f14282,f223])).
% 12.62/2.06  fof(f14282,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | spl9_235),
% 12.62/2.06    inference(resolution,[],[f14051,f168])).
% 12.62/2.06  fof(f14051,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0)) | spl9_235),
% 12.62/2.06    inference(avatar_component_clause,[],[f14050])).
% 12.62/2.06  fof(f20802,plain,(
% 12.62/2.06    spl9_336 | ~spl9_3),
% 12.62/2.06    inference(avatar_split_clause,[],[f20801,f293,f20798])).
% 12.62/2.06  fof(f20801,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))) | ~spl9_3),
% 12.62/2.06    inference(forward_demodulation,[],[f19869,f122])).
% 12.62/2.06  fof(f122,plain,(
% 12.62/2.06    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.62/2.06    inference(cnf_transformation,[],[f14])).
% 12.62/2.06  fof(f14,axiom,(
% 12.62/2.06    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 12.62/2.06  fof(f19869,plain,(
% 12.62/2.06    r1_tarski(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3))) | ~spl9_3),
% 12.62/2.06    inference(superposition,[],[f14311,f374])).
% 12.62/2.06  fof(f14311,plain,(
% 12.62/2.06    ( ! [X0] : (r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),X0)))) ) | ~spl9_3),
% 12.62/2.06    inference(resolution,[],[f343,f229])).
% 12.62/2.06  fof(f229,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 12.62/2.06    inference(definition_unfolding,[],[f165,f131,f131])).
% 12.62/2.06  fof(f165,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f62])).
% 12.62/2.06  fof(f62,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 12.62/2.06    inference(ennf_transformation,[],[f10])).
% 12.62/2.06  fof(f10,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 12.62/2.06  fof(f20376,plain,(
% 12.62/2.06    k1_tarski(sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK1 != sK2 | k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f20294,plain,(
% 12.62/2.06    sK1 != sK2 | k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3) | k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f20269,plain,(
% 12.62/2.06    k1_tarski(sK0) != k4_xboole_0(sK3,k1_tarski(sK1)) | sK3 != k4_xboole_0(sK3,k1_tarski(sK1)) | sK3 = k1_tarski(sK0)),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f20154,plain,(
% 12.62/2.06    ~spl9_119 | spl9_214),
% 12.62/2.06    inference(avatar_split_clause,[],[f17358,f12366,f9178])).
% 12.62/2.06  fof(f9178,plain,(
% 12.62/2.06    spl9_119 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).
% 12.62/2.06  fof(f12366,plain,(
% 12.62/2.06    spl9_214 <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).
% 12.62/2.06  fof(f17358,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k1_tarski(sK0)) | spl9_214),
% 12.62/2.06    inference(resolution,[],[f10824,f13258])).
% 12.62/2.06  fof(f13258,plain,(
% 12.62/2.06    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) | spl9_214),
% 12.62/2.06    inference(avatar_component_clause,[],[f12366])).
% 12.62/2.06  fof(f20146,plain,(
% 12.62/2.06    spl9_106 | ~spl9_105),
% 12.62/2.06    inference(avatar_split_clause,[],[f18538,f7911,f7914])).
% 12.62/2.06  fof(f7914,plain,(
% 12.62/2.06    spl9_106 <=> sK3 = k4_xboole_0(sK3,k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).
% 12.62/2.06  fof(f18538,plain,(
% 12.62/2.06    sK3 = k4_xboole_0(sK3,k1_tarski(sK1)) | ~spl9_105),
% 12.62/2.06    inference(forward_demodulation,[],[f18537,f121])).
% 12.62/2.06  fof(f18537,plain,(
% 12.62/2.06    k2_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK1)) | ~spl9_105),
% 12.62/2.06    inference(forward_demodulation,[],[f18536,f394])).
% 12.62/2.06  fof(f18536,plain,(
% 12.62/2.06    k4_xboole_0(sK3,k1_tarski(sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),sK3))) | ~spl9_105),
% 12.62/2.06    inference(forward_demodulation,[],[f18528,f160])).
% 12.62/2.06  fof(f18528,plain,(
% 12.62/2.06    k4_xboole_0(sK3,k1_tarski(sK1)) = k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),sK3)) | ~spl9_105),
% 12.62/2.06    inference(resolution,[],[f18494,f135])).
% 12.62/2.06  fof(f18494,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl9_105),
% 12.62/2.06    inference(avatar_component_clause,[],[f7911])).
% 12.62/2.06  fof(f19210,plain,(
% 12.62/2.06    spl9_38 | ~spl9_23),
% 12.62/2.06    inference(avatar_split_clause,[],[f6968,f424,f6345])).
% 12.62/2.06  fof(f424,plain,(
% 12.62/2.06    spl9_23 <=> sK3 = k2_xboole_0(k1_tarski(sK1),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 12.62/2.06  fof(f6968,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK1),sK3) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f6894,f126])).
% 12.62/2.06  fof(f6894,plain,(
% 12.62/2.06    ( ! [X0] : (r1_tarski(k1_tarski(sK1),k2_xboole_0(sK3,X0))) ) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f6568,f129])).
% 12.62/2.06  fof(f6568,plain,(
% 12.62/2.06    ( ! [X3] : (r1_tarski(k1_tarski(sK1),k2_xboole_0(X3,sK3))) ) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f581,f6444])).
% 12.62/2.06  fof(f6444,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK1),sK3) | ~spl9_23),
% 12.62/2.06    inference(avatar_component_clause,[],[f424])).
% 12.62/2.06  fof(f581,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 12.62/2.06    inference(resolution,[],[f550,f164])).
% 12.62/2.06  fof(f164,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 12.62/2.06    inference(cnf_transformation,[],[f61])).
% 12.62/2.06  fof(f61,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 12.62/2.06    inference(ennf_transformation,[],[f7])).
% 12.62/2.06  fof(f7,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 12.62/2.06  fof(f550,plain,(
% 12.62/2.06    ( ! [X2,X3] : (r1_tarski(X3,k2_xboole_0(X3,X2))) )),
% 12.62/2.06    inference(superposition,[],[f521,f129])).
% 12.62/2.06  fof(f521,plain,(
% 12.62/2.06    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 12.62/2.06    inference(resolution,[],[f164,f255])).
% 12.62/2.06  fof(f255,plain,(
% 12.62/2.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.62/2.06    inference(equality_resolution,[],[f138])).
% 12.62/2.06  fof(f138,plain,(
% 12.62/2.06    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.62/2.06    inference(cnf_transformation,[],[f76])).
% 12.62/2.06  fof(f76,plain,(
% 12.62/2.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.62/2.06    inference(flattening,[],[f75])).
% 12.62/2.06  fof(f75,plain,(
% 12.62/2.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.62/2.06    inference(nnf_transformation,[],[f5])).
% 12.62/2.06  fof(f5,axiom,(
% 12.62/2.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.62/2.06  fof(f19201,plain,(
% 12.62/2.06    spl9_25 | ~spl9_23),
% 12.62/2.06    inference(avatar_split_clause,[],[f6861,f424,f445])).
% 12.62/2.06  fof(f6861,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(sK3,k1_tarski(sK1)) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f129,f6444])).
% 12.62/2.06  fof(f19171,plain,(
% 12.62/2.06    ~spl9_3 | spl9_88),
% 12.62/2.06    inference(avatar_split_clause,[],[f13950,f7683,f293])).
% 12.62/2.06  fof(f7683,plain,(
% 12.62/2.06    spl9_88 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 12.62/2.06  fof(f13950,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | spl9_88),
% 12.62/2.06    inference(resolution,[],[f7684,f168])).
% 12.62/2.06  fof(f7684,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl9_88),
% 12.62/2.06    inference(avatar_component_clause,[],[f7683])).
% 12.62/2.06  fof(f19118,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) != k2_xboole_0(sK3,k1_tarski(sK2)) | ~r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2))) | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f19054,plain,(
% 12.62/2.06    spl9_301 | ~spl9_18 | ~spl9_36 | ~spl9_62 | ~spl9_121),
% 12.62/2.06    inference(avatar_split_clause,[],[f19050,f9192,f7167,f6318,f377,f19052])).
% 12.62/2.06  fof(f19052,plain,(
% 12.62/2.06    spl9_301 <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_301])])).
% 12.62/2.06  fof(f7167,plain,(
% 12.62/2.06    spl9_62 <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 12.62/2.06  fof(f9192,plain,(
% 12.62/2.06    spl9_121 <=> sK0 = sK1),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).
% 12.62/2.06  fof(f19050,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k1_tarski(sK2)) | (~spl9_18 | ~spl9_36 | ~spl9_62 | ~spl9_121)),
% 12.62/2.06    inference(forward_demodulation,[],[f19049,f121])).
% 12.62/2.06  fof(f19049,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k1_xboole_0)) | (~spl9_18 | ~spl9_36 | ~spl9_62 | ~spl9_121)),
% 12.62/2.06    inference(forward_demodulation,[],[f19048,f2136])).
% 12.62/2.06  fof(f2136,plain,(
% 12.62/2.06    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) )),
% 12.62/2.06    inference(resolution,[],[f134,f263])).
% 12.62/2.06  fof(f263,plain,(
% 12.62/2.06    ( ! [X4,X1] : (r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1)))) )),
% 12.62/2.06    inference(equality_resolution,[],[f262])).
% 12.62/2.06  fof(f262,plain,(
% 12.62/2.06    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2) )),
% 12.62/2.06    inference(equality_resolution,[],[f235])).
% 12.62/2.06  fof(f235,plain,(
% 12.62/2.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2) )),
% 12.62/2.06    inference(definition_unfolding,[],[f171,f130])).
% 12.62/2.06  fof(f171,plain,(
% 12.62/2.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 12.62/2.06    inference(cnf_transformation,[],[f95])).
% 12.62/2.06  fof(f19048,plain,(
% 12.62/2.06    k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k1_xboole_0)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) | (~spl9_18 | ~spl9_36 | ~spl9_62 | ~spl9_121)),
% 12.62/2.06    inference(forward_demodulation,[],[f19047,f378])).
% 12.62/2.06  fof(f378,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3) | ~spl9_18),
% 12.62/2.06    inference(avatar_component_clause,[],[f377])).
% 12.62/2.06  fof(f19047,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK0),sK3))) | (~spl9_18 | ~spl9_36 | ~spl9_62 | ~spl9_121)),
% 12.62/2.06    inference(forward_demodulation,[],[f18744,f9193])).
% 12.62/2.06  fof(f9193,plain,(
% 12.62/2.06    sK0 = sK1 | ~spl9_121),
% 12.62/2.06    inference(avatar_component_clause,[],[f9192])).
% 12.62/2.06  fof(f18744,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK1),sK3))) | (~spl9_18 | ~spl9_36 | ~spl9_62)),
% 12.62/2.06    inference(forward_demodulation,[],[f17555,f14279])).
% 12.62/2.06  fof(f14279,plain,(
% 12.62/2.06    ( ! [X0] : (k2_xboole_0(k1_tarski(sK2),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,k1_tarski(sK2)),sK3)) ) | ~spl9_62),
% 12.62/2.06    inference(forward_demodulation,[],[f14273,f129])).
% 12.62/2.06  fof(f14273,plain,(
% 12.62/2.06    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_tarski(sK2)),sK3) = k2_xboole_0(k4_xboole_0(X0,sK3),k1_tarski(sK2))) ) | ~spl9_62),
% 12.62/2.06    inference(superposition,[],[f163,f7168])).
% 12.62/2.06  fof(f7168,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) | ~spl9_62),
% 12.62/2.06    inference(avatar_component_clause,[],[f7167])).
% 12.62/2.06  fof(f17555,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)) | (~spl9_18 | ~spl9_36)),
% 12.62/2.06    inference(superposition,[],[f6319,f14168])).
% 12.62/2.06  fof(f14168,plain,(
% 12.62/2.06    ( ! [X1] : (k4_xboole_0(X1,sK3) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X1),sK3)) ) | ~spl9_18),
% 12.62/2.06    inference(forward_demodulation,[],[f14162,f392])).
% 12.62/2.06  fof(f14162,plain,(
% 12.62/2.06    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X1),sK3)) ) | ~spl9_18),
% 12.62/2.06    inference(superposition,[],[f163,f378])).
% 12.62/2.06  fof(f18646,plain,(
% 12.62/2.06    sK3 != k4_xboole_0(sK3,k1_tarski(sK0)) | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f18616,plain,(
% 12.62/2.06    spl9_91 | ~spl9_3 | ~spl9_69 | ~spl9_106 | ~spl9_159),
% 12.62/2.06    inference(avatar_split_clause,[],[f18614,f9957,f7914,f7487,f293,f7700])).
% 12.62/2.06  fof(f7487,plain,(
% 12.62/2.06    spl9_69 <=> k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 12.62/2.06  fof(f9957,plain,(
% 12.62/2.06    spl9_159 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).
% 12.62/2.06  fof(f18614,plain,(
% 12.62/2.06    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) | (~spl9_3 | ~spl9_69 | ~spl9_106 | ~spl9_159)),
% 12.62/2.06    inference(forward_demodulation,[],[f18613,f7488])).
% 12.62/2.06  fof(f7488,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) | ~spl9_69),
% 12.62/2.06    inference(avatar_component_clause,[],[f7487])).
% 12.62/2.06  fof(f18613,plain,(
% 12.62/2.06    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))) | (~spl9_3 | ~spl9_106 | ~spl9_159)),
% 12.62/2.06    inference(forward_demodulation,[],[f18612,f10583])).
% 12.62/2.06  fof(f10583,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 12.62/2.06    inference(forward_demodulation,[],[f10496,f392])).
% 12.62/2.06  fof(f10496,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) )),
% 12.62/2.06    inference(superposition,[],[f163,f374])).
% 12.62/2.06  fof(f18612,plain,(
% 12.62/2.06    r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK1)))) | (~spl9_3 | ~spl9_106 | ~spl9_159)),
% 12.62/2.06    inference(forward_demodulation,[],[f18579,f10520])).
% 12.62/2.06  fof(f10520,plain,(
% 12.62/2.06    ( ! [X47] : (k4_xboole_0(k2_xboole_0(k1_tarski(sK0),X47),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(X47,k1_tarski(sK1)))) ) | ~spl9_159),
% 12.62/2.06    inference(superposition,[],[f163,f9958])).
% 12.62/2.06  fof(f9958,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl9_159),
% 12.62/2.06    inference(avatar_component_clause,[],[f9957])).
% 12.62/2.06  fof(f18579,plain,(
% 12.62/2.06    r1_tarski(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK1))) | (~spl9_3 | ~spl9_106)),
% 12.62/2.06    inference(superposition,[],[f14312,f7915])).
% 12.62/2.06  fof(f7915,plain,(
% 12.62/2.06    sK3 = k4_xboole_0(sK3,k1_tarski(sK1)) | ~spl9_106),
% 12.62/2.06    inference(avatar_component_clause,[],[f7914])).
% 12.62/2.06  fof(f15514,plain,(
% 12.62/2.06    spl9_226),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f15513])).
% 12.62/2.06  fof(f15513,plain,(
% 12.62/2.06    $false | spl9_226),
% 12.62/2.06    inference(trivial_inequality_removal,[],[f15509])).
% 12.62/2.06  fof(f15509,plain,(
% 12.62/2.06    k1_xboole_0 != k1_xboole_0 | spl9_226),
% 12.62/2.06    inference(superposition,[],[f13964,f277])).
% 12.62/2.06  fof(f277,plain,(
% 12.62/2.06    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 12.62/2.06    inference(equality_resolution,[],[f251])).
% 12.62/2.06  fof(f251,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X2) != X0) )),
% 12.62/2.06    inference(definition_unfolding,[],[f198,f130])).
% 12.62/2.06  fof(f198,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 12.62/2.06    inference(cnf_transformation,[],[f108])).
% 12.62/2.06  fof(f108,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 12.62/2.06    inference(flattening,[],[f107])).
% 12.62/2.06  fof(f107,plain,(
% 12.62/2.06    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 12.62/2.06    inference(nnf_transformation,[],[f69])).
% 12.62/2.06  fof(f69,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 12.62/2.06    inference(ennf_transformation,[],[f48])).
% 12.62/2.06  fof(f48,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 12.62/2.06  fof(f13964,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl9_226),
% 12.62/2.06    inference(avatar_component_clause,[],[f13963])).
% 12.62/2.06  fof(f13963,plain,(
% 12.62/2.06    spl9_226 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).
% 12.62/2.06  fof(f14705,plain,(
% 12.62/2.06    spl9_246),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f14701])).
% 12.62/2.06  fof(f14701,plain,(
% 12.62/2.06    $false | spl9_246),
% 12.62/2.06    inference(resolution,[],[f14699,f550])).
% 12.62/2.06  fof(f14699,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2))) | spl9_246),
% 12.62/2.06    inference(avatar_component_clause,[],[f14698])).
% 12.62/2.06  fof(f14698,plain,(
% 12.62/2.06    spl9_246 <=> r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).
% 12.62/2.06  fof(f14700,plain,(
% 12.62/2.06    ~spl9_246 | spl9_43 | ~spl9_145),
% 12.62/2.06    inference(avatar_split_clause,[],[f14689,f9437,f6408,f14698])).
% 12.62/2.06  fof(f9437,plain,(
% 12.62/2.06    spl9_145 <=> r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).
% 12.62/2.06  fof(f14689,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) | ~r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2))) | ~spl9_145),
% 12.62/2.06    inference(resolution,[],[f14673,f139])).
% 12.62/2.06  fof(f139,plain,(
% 12.62/2.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f76])).
% 12.62/2.06  fof(f14673,plain,(
% 12.62/2.06    r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) | ~spl9_145),
% 12.62/2.06    inference(avatar_component_clause,[],[f9437])).
% 12.62/2.06  fof(f14682,plain,(
% 12.62/2.06    spl9_244),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f14679])).
% 12.62/2.06  fof(f14679,plain,(
% 12.62/2.06    $false | spl9_244),
% 12.62/2.06    inference(resolution,[],[f14676,f118])).
% 12.62/2.06  fof(f118,plain,(
% 12.62/2.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f12])).
% 12.62/2.06  fof(f12,axiom,(
% 12.62/2.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 12.62/2.06  fof(f14676,plain,(
% 12.62/2.06    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | spl9_244),
% 12.62/2.06    inference(avatar_component_clause,[],[f14675])).
% 12.62/2.06  fof(f14675,plain,(
% 12.62/2.06    spl9_244 <=> r1_tarski(k1_xboole_0,k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).
% 12.62/2.06  fof(f14677,plain,(
% 12.62/2.06    spl9_145 | ~spl9_244 | ~spl9_21 | ~spl9_240),
% 12.62/2.06    inference(avatar_split_clause,[],[f14662,f14115,f401,f14675,f9437])).
% 12.62/2.06  fof(f14115,plain,(
% 12.62/2.06    spl9_240 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).
% 12.62/2.06  fof(f14662,plain,(
% 12.62/2.06    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | r1_tarski(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) | (~spl9_21 | ~spl9_240)),
% 12.62/2.06    inference(superposition,[],[f14191,f14116])).
% 12.62/2.06  fof(f14116,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK2)),sK3) | ~spl9_240),
% 12.62/2.06    inference(avatar_component_clause,[],[f14115])).
% 12.62/2.06  fof(f14191,plain,(
% 12.62/2.06    ( ! [X4] : (~r1_tarski(k4_xboole_0(X4,sK3),k1_tarski(sK0)) | r1_tarski(X4,sK3)) ) | ~spl9_21),
% 12.62/2.06    inference(superposition,[],[f169,f6718])).
% 12.62/2.06  fof(f169,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f66])).
% 12.62/2.06  fof(f66,plain,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.62/2.06    inference(ennf_transformation,[],[f19])).
% 12.62/2.06  fof(f19,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 12.62/2.06  fof(f14131,plain,(
% 12.62/2.06    ~spl9_91 | spl9_92),
% 12.62/2.06    inference(avatar_split_clause,[],[f7721,f7706,f7700])).
% 12.62/2.06  fof(f7706,plain,(
% 12.62/2.06    spl9_92 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).
% 12.62/2.06  fof(f7721,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) | spl9_92),
% 12.62/2.06    inference(resolution,[],[f7707,f168])).
% 12.62/2.06  fof(f7707,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2)) | spl9_92),
% 12.62/2.06    inference(avatar_component_clause,[],[f7706])).
% 12.62/2.06  fof(f14128,plain,(
% 12.62/2.06    spl9_79 | ~spl9_37 | ~spl9_39 | ~spl9_62),
% 12.62/2.06    inference(avatar_split_clause,[],[f8103,f7167,f6349,f6341,f7592])).
% 12.62/2.06  fof(f7592,plain,(
% 12.62/2.06    spl9_79 <=> r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).
% 12.62/2.06  fof(f6341,plain,(
% 12.62/2.06    spl9_37 <=> r1_tarski(k1_tarski(sK0),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 12.62/2.06  fof(f8103,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2))) | (~spl9_37 | ~spl9_39 | ~spl9_62)),
% 12.62/2.06    inference(superposition,[],[f7965,f7168])).
% 12.62/2.06  fof(f7965,plain,(
% 12.62/2.06    ( ! [X1] : (r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k4_xboole_0(X1,sK3)))) ) | (~spl9_37 | ~spl9_39)),
% 12.62/2.06    inference(superposition,[],[f7313,f7150])).
% 12.62/2.06  fof(f7150,plain,(
% 12.62/2.06    ( ! [X21] : (k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(X21,sK3))) ) | ~spl9_39),
% 12.62/2.06    inference(resolution,[],[f154,f6611])).
% 12.62/2.06  fof(f6611,plain,(
% 12.62/2.06    ( ! [X1] : (~r2_hidden(sK0,k4_xboole_0(X1,sK3))) ) | ~spl9_39),
% 12.62/2.06    inference(resolution,[],[f6350,f266])).
% 12.62/2.06  fof(f6350,plain,(
% 12.62/2.06    r2_hidden(sK0,sK3) | ~spl9_39),
% 12.62/2.06    inference(avatar_component_clause,[],[f6349])).
% 12.62/2.06  fof(f154,plain,(
% 12.62/2.06    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f88])).
% 12.62/2.06  fof(f88,plain,(
% 12.62/2.06    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 12.62/2.06    inference(nnf_transformation,[],[f35])).
% 12.62/2.06  fof(f35,axiom,(
% 12.62/2.06    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 12.62/2.06  fof(f7313,plain,(
% 12.62/2.06    ( ! [X41] : (r1_tarski(k4_xboole_0(k1_tarski(sK0),X41),k4_xboole_0(sK3,X41))) ) | ~spl9_37),
% 12.62/2.06    inference(resolution,[],[f166,f6342])).
% 12.62/2.06  fof(f6342,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),sK3) | ~spl9_37),
% 12.62/2.06    inference(avatar_component_clause,[],[f6341])).
% 12.62/2.06  fof(f14087,plain,(
% 12.62/2.06    spl9_22 | spl9_13 | ~spl9_85),
% 12.62/2.06    inference(avatar_split_clause,[],[f12215,f7641,f332,f419])).
% 12.62/2.06  fof(f332,plain,(
% 12.62/2.06    spl9_13 <=> sK3 = k1_tarski(sK0)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 12.62/2.06  fof(f7641,plain,(
% 12.62/2.06    spl9_85 <=> k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).
% 12.62/2.06  fof(f12215,plain,(
% 12.62/2.06    sK3 = k1_tarski(sK0) | r2_hidden(sK2,sK3) | ~spl9_85),
% 12.62/2.06    inference(superposition,[],[f7642,f152])).
% 12.62/2.06  fof(f7642,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2)) | ~spl9_85),
% 12.62/2.06    inference(avatar_component_clause,[],[f7641])).
% 12.62/2.06  fof(f14052,plain,(
% 12.62/2.06    ~spl9_235 | spl9_120 | ~spl9_194),
% 12.62/2.06    inference(avatar_split_clause,[],[f12103,f11033,f9181,f14050])).
% 12.62/2.06  fof(f9181,plain,(
% 12.62/2.06    spl9_120 <=> k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).
% 12.62/2.06  fof(f11033,plain,(
% 12.62/2.06    spl9_194 <=> r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).
% 12.62/2.06  fof(f12103,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK1)) | ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK0)) | ~spl9_194),
% 12.62/2.06    inference(resolution,[],[f11034,f139])).
% 12.62/2.06  fof(f11034,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl9_194),
% 12.62/2.06    inference(avatar_component_clause,[],[f11033])).
% 12.62/2.06  fof(f13972,plain,(
% 12.62/2.06    k1_tarski(sK2) != k4_xboole_0(sK3,k1_tarski(sK0)) | sK3 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0))) | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f13965,plain,(
% 12.62/2.06    ~spl9_226 | spl9_88 | ~spl9_218),
% 12.62/2.06    inference(avatar_split_clause,[],[f13961,f12778,f7683,f13963])).
% 12.62/2.06  fof(f12778,plain,(
% 12.62/2.06    spl9_218 <=> k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).
% 12.62/2.06  fof(f13961,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | (spl9_88 | ~spl9_218)),
% 12.62/2.06    inference(forward_demodulation,[],[f13949,f12779])).
% 12.62/2.06  fof(f12779,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0)) | ~spl9_218),
% 12.62/2.06    inference(avatar_component_clause,[],[f12778])).
% 12.62/2.06  fof(f13949,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl9_88),
% 12.62/2.06    inference(resolution,[],[f7684,f147])).
% 12.62/2.06  fof(f147,plain,(
% 12.62/2.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 12.62/2.06    inference(cnf_transformation,[],[f85])).
% 12.62/2.06  fof(f85,plain,(
% 12.62/2.06    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 12.62/2.06    inference(nnf_transformation,[],[f6])).
% 12.62/2.06  fof(f6,axiom,(
% 12.62/2.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 12.62/2.06  fof(f13680,plain,(
% 12.62/2.06    spl9_223 | ~spl9_24),
% 12.62/2.06    inference(avatar_split_clause,[],[f13669,f437,f13678])).
% 12.62/2.06  fof(f13678,plain,(
% 12.62/2.06    spl9_223 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_223])])).
% 12.62/2.06  fof(f13669,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),sK3) | ~spl9_24),
% 12.62/2.06    inference(superposition,[],[f394,f11550])).
% 12.62/2.06  fof(f11550,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))) | ~spl9_24),
% 12.62/2.06    inference(avatar_component_clause,[],[f437])).
% 12.62/2.06  fof(f13259,plain,(
% 12.62/2.06    spl9_38 | ~spl9_214 | ~spl9_21 | ~spl9_203),
% 12.62/2.06    inference(avatar_split_clause,[],[f13254,f11651,f401,f12366,f6345])).
% 12.62/2.06  fof(f11651,plain,(
% 12.62/2.06    spl9_203 <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_203])])).
% 12.62/2.06  fof(f13254,plain,(
% 12.62/2.06    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) | r1_tarski(k1_tarski(sK1),sK3) | (~spl9_21 | ~spl9_203)),
% 12.62/2.06    inference(superposition,[],[f11275,f11652])).
% 12.62/2.06  fof(f11652,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3) | ~spl9_203),
% 12.62/2.06    inference(avatar_component_clause,[],[f11651])).
% 12.62/2.06  fof(f11275,plain,(
% 12.62/2.06    ( ! [X16] : (~r1_tarski(k4_xboole_0(X16,sK3),k1_tarski(sK0)) | r1_tarski(X16,sK3)) ) | ~spl9_21),
% 12.62/2.06    inference(superposition,[],[f169,f6718])).
% 12.62/2.06  fof(f12781,plain,(
% 12.62/2.06    ~spl9_92 | spl9_218 | ~spl9_216),
% 12.62/2.06    inference(avatar_split_clause,[],[f12764,f12756,f12778,f7706])).
% 12.62/2.06  fof(f12756,plain,(
% 12.62/2.06    spl9_216 <=> r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).
% 12.62/2.06  fof(f12764,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0)) | ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2)) | ~spl9_216),
% 12.62/2.06    inference(resolution,[],[f12757,f139])).
% 12.62/2.06  fof(f12757,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0))) | ~spl9_216),
% 12.62/2.06    inference(avatar_component_clause,[],[f12756])).
% 12.62/2.06  fof(f12780,plain,(
% 12.62/2.06    spl9_218 | ~spl9_4 | ~spl9_216),
% 12.62/2.06    inference(avatar_split_clause,[],[f12776,f12756,f296,f12778])).
% 12.62/2.06  fof(f296,plain,(
% 12.62/2.06    spl9_4 <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 12.62/2.06  fof(f12776,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0)) | (~spl9_4 | ~spl9_216)),
% 12.62/2.06    inference(forward_demodulation,[],[f12775,f121])).
% 12.62/2.06  fof(f12775,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK2),k1_xboole_0) = k4_xboole_0(sK3,k1_tarski(sK0)) | (~spl9_4 | ~spl9_216)),
% 12.62/2.06    inference(forward_demodulation,[],[f12774,f374])).
% 12.62/2.06  fof(f12774,plain,(
% 12.62/2.06    k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK3,sK3)) | (~spl9_4 | ~spl9_216)),
% 12.62/2.06    inference(forward_demodulation,[],[f12773,f350])).
% 12.62/2.06  fof(f350,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | ~spl9_4),
% 12.62/2.06    inference(avatar_component_clause,[],[f296])).
% 12.62/2.06  fof(f12773,plain,(
% 12.62/2.06    k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))) | ~spl9_216),
% 12.62/2.06    inference(forward_demodulation,[],[f12763,f160])).
% 12.62/2.06  fof(f12763,plain,(
% 12.62/2.06    k4_xboole_0(sK3,k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))) | ~spl9_216),
% 12.62/2.06    inference(resolution,[],[f12757,f135])).
% 12.62/2.06  fof(f12758,plain,(
% 12.62/2.06    spl9_216 | ~spl9_81 | ~spl9_111),
% 12.62/2.06    inference(avatar_split_clause,[],[f12739,f8261,f7603,f12756])).
% 12.62/2.06  fof(f12739,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK2),k4_xboole_0(sK3,k1_tarski(sK0))) | (~spl9_81 | ~spl9_111)),
% 12.62/2.06    inference(superposition,[],[f11658,f7604])).
% 12.62/2.06  fof(f11658,plain,(
% 12.62/2.06    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_tarski(sK2),X0),k4_xboole_0(sK3,X0))) ) | ~spl9_111),
% 12.62/2.06    inference(resolution,[],[f8262,f166])).
% 12.62/2.06  fof(f8262,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK2),sK3) | ~spl9_111),
% 12.62/2.06    inference(avatar_component_clause,[],[f8261])).
% 12.62/2.06  fof(f12214,plain,(
% 12.62/2.06    ~spl9_210 | spl9_207),
% 12.62/2.06    inference(avatar_split_clause,[],[f12210,f12097,f12212])).
% 12.62/2.06  fof(f12212,plain,(
% 12.62/2.06    spl9_210 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).
% 12.62/2.06  fof(f12210,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl9_207),
% 12.62/2.06    inference(resolution,[],[f12098,f147])).
% 12.62/2.06  fof(f12099,plain,(
% 12.62/2.06    ~spl9_207 | spl9_166),
% 12.62/2.06    inference(avatar_split_clause,[],[f12090,f10035,f12097])).
% 12.62/2.06  fof(f10035,plain,(
% 12.62/2.06    spl9_166 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).
% 12.62/2.06  fof(f12090,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl9_166),
% 12.62/2.06    inference(resolution,[],[f10036,f168])).
% 12.62/2.06  fof(f10036,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1)) | spl9_166),
% 12.62/2.06    inference(avatar_component_clause,[],[f10035])).
% 12.62/2.06  fof(f11681,plain,(
% 12.62/2.06    spl9_205 | ~spl9_63),
% 12.62/2.06    inference(avatar_split_clause,[],[f11670,f7186,f11679])).
% 12.62/2.06  fof(f11679,plain,(
% 12.62/2.06    spl9_205 <=> k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_205])])).
% 12.62/2.06  fof(f7186,plain,(
% 12.62/2.06    spl9_63 <=> r2_hidden(sK1,k1_tarski(sK2))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).
% 12.62/2.06  fof(f11670,plain,(
% 12.62/2.06    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~spl9_63),
% 12.62/2.06    inference(resolution,[],[f11338,f134])).
% 12.62/2.06  fof(f11338,plain,(
% 12.62/2.06    r2_hidden(sK1,k1_tarski(sK2)) | ~spl9_63),
% 12.62/2.06    inference(avatar_component_clause,[],[f7186])).
% 12.62/2.06  fof(f11675,plain,(
% 12.62/2.06    spl9_204 | ~spl9_63),
% 12.62/2.06    inference(avatar_split_clause,[],[f11666,f7186,f11673])).
% 12.62/2.06  fof(f11673,plain,(
% 12.62/2.06    spl9_204 <=> sK1 = sK2),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).
% 12.62/2.06  fof(f11666,plain,(
% 12.62/2.06    sK1 = sK2 | ~spl9_63),
% 12.62/2.06    inference(resolution,[],[f11338,f259])).
% 12.62/2.06  fof(f259,plain,(
% 12.62/2.06    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 12.62/2.06    inference(equality_resolution,[],[f143])).
% 12.62/2.06  fof(f143,plain,(
% 12.62/2.06    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 12.62/2.06    inference(cnf_transformation,[],[f84])).
% 12.62/2.06  fof(f11653,plain,(
% 12.62/2.06    spl9_203 | spl9_35),
% 12.62/2.06    inference(avatar_split_clause,[],[f11648,f3386,f11651])).
% 12.62/2.06  fof(f11648,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3) | spl9_35),
% 12.62/2.06    inference(resolution,[],[f11591,f154])).
% 12.62/2.06  fof(f11591,plain,(
% 12.62/2.06    ~r2_hidden(sK1,sK3) | spl9_35),
% 12.62/2.06    inference(avatar_component_clause,[],[f3386])).
% 12.62/2.06  fof(f11571,plain,(
% 12.62/2.06    spl9_111 | ~spl9_4),
% 12.62/2.06    inference(avatar_split_clause,[],[f11315,f296,f8261])).
% 12.62/2.06  fof(f11315,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK2),sK3) | ~spl9_4),
% 12.62/2.06    inference(superposition,[],[f269,f350])).
% 12.62/2.06  fof(f269,plain,(
% 12.62/2.06    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 12.62/2.06    inference(equality_resolution,[],[f238])).
% 12.62/2.06  fof(f238,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X2) != X0) )),
% 12.62/2.06    inference(definition_unfolding,[],[f185,f130])).
% 12.62/2.06  fof(f185,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 12.62/2.06    inference(cnf_transformation,[],[f102])).
% 12.62/2.06  fof(f11434,plain,(
% 12.62/2.06    sK0 != sK2 | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) | sK3 = k1_tarski(sK2)),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f11355,plain,(
% 12.62/2.06    spl9_198 | ~spl9_80),
% 12.62/2.06    inference(avatar_split_clause,[],[f11344,f7596,f11353])).
% 12.62/2.06  fof(f11353,plain,(
% 12.62/2.06    spl9_198 <=> k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).
% 12.62/2.06  fof(f7596,plain,(
% 12.62/2.06    spl9_80 <=> r2_hidden(sK2,k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).
% 12.62/2.06  fof(f11344,plain,(
% 12.62/2.06    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) | ~spl9_80),
% 12.62/2.06    inference(resolution,[],[f11336,f134])).
% 12.62/2.06  fof(f11336,plain,(
% 12.62/2.06    r2_hidden(sK2,k1_tarski(sK0)) | ~spl9_80),
% 12.62/2.06    inference(avatar_component_clause,[],[f7596])).
% 12.62/2.06  fof(f11349,plain,(
% 12.62/2.06    spl9_197 | ~spl9_80),
% 12.62/2.06    inference(avatar_split_clause,[],[f11340,f7596,f11347])).
% 12.62/2.06  fof(f11340,plain,(
% 12.62/2.06    sK0 = sK2 | ~spl9_80),
% 12.62/2.06    inference(resolution,[],[f11336,f259])).
% 12.62/2.06  fof(f11035,plain,(
% 12.62/2.06    spl9_194 | ~spl9_37 | ~spl9_159),
% 12.62/2.06    inference(avatar_split_clause,[],[f10139,f9957,f6341,f11033])).
% 12.62/2.06  fof(f10139,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1))) | (~spl9_37 | ~spl9_159)),
% 12.62/2.06    inference(superposition,[],[f7313,f9958])).
% 12.62/2.06  fof(f10991,plain,(
% 12.62/2.06    spl9_37 | ~spl9_19),
% 12.62/2.06    inference(avatar_split_clause,[],[f6947,f385,f6341])).
% 12.62/2.06  fof(f6947,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),sK3) | ~spl9_19),
% 12.62/2.06    inference(superposition,[],[f550,f6719])).
% 12.62/2.06  fof(f10981,plain,(
% 12.62/2.06    spl9_21 | ~spl9_19),
% 12.62/2.06    inference(avatar_split_clause,[],[f6930,f385,f401])).
% 12.62/2.06  fof(f6930,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(sK3,k1_tarski(sK0)) | ~spl9_19),
% 12.62/2.06    inference(superposition,[],[f6719,f129])).
% 12.62/2.06  fof(f10910,plain,(
% 12.62/2.06    k1_tarski(sK0) != k4_xboole_0(sK3,k1_tarski(sK1)) | k1_tarski(sK1) != k4_xboole_0(sK3,k1_tarski(sK0)) | sK3 != k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))) | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 12.62/2.06    introduced(theory_tautology_sat_conflict,[])).
% 12.62/2.06  fof(f10883,plain,(
% 12.62/2.06    ~spl9_7 | spl9_172),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f10879])).
% 12.62/2.06  fof(f10879,plain,(
% 12.62/2.06    $false | (~spl9_7 | spl9_172)),
% 12.62/2.06    inference(resolution,[],[f10854,f6781])).
% 12.62/2.06  fof(f6781,plain,(
% 12.62/2.06    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK3,X0))) ) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f6331,f129])).
% 12.62/2.06  fof(f6331,plain,(
% 12.62/2.06    ( ! [X3] : (r2_hidden(sK0,k2_xboole_0(X3,sK3))) ) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f2970,f348])).
% 12.62/2.06  fof(f348,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl9_7),
% 12.62/2.06    inference(avatar_component_clause,[],[f308])).
% 12.62/2.06  fof(f308,plain,(
% 12.62/2.06    spl9_7 <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 12.62/2.06  fof(f2970,plain,(
% 12.62/2.06    ( ! [X10,X8,X9] : (r2_hidden(X8,k2_xboole_0(X9,k2_xboole_0(k1_tarski(X8),X10)))) )),
% 12.62/2.06    inference(resolution,[],[f2961,f581])).
% 12.62/2.06  fof(f10854,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2))) | spl9_172),
% 12.62/2.06    inference(avatar_component_clause,[],[f10853])).
% 12.62/2.06  fof(f10853,plain,(
% 12.62/2.06    spl9_172 <=> r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).
% 12.62/2.06  fof(f10874,plain,(
% 12.62/2.06    ~spl9_23 | spl9_171),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f10870])).
% 12.62/2.06  fof(f10870,plain,(
% 12.62/2.06    $false | (~spl9_23 | spl9_171)),
% 12.62/2.06    inference(resolution,[],[f10851,f6808])).
% 12.62/2.06  fof(f6808,plain,(
% 12.62/2.06    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(sK3,X0))) ) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f6558,f129])).
% 12.62/2.06  fof(f6558,plain,(
% 12.62/2.06    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(X0,sK3))) ) | ~spl9_23),
% 12.62/2.06    inference(superposition,[],[f2970,f6444])).
% 12.62/2.06  fof(f10851,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2))) | spl9_171),
% 12.62/2.06    inference(avatar_component_clause,[],[f10850])).
% 12.62/2.06  fof(f10850,plain,(
% 12.62/2.06    spl9_171 <=> r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_171])])).
% 12.62/2.06  fof(f10855,plain,(
% 12.62/2.06    ~spl9_171 | ~spl9_172 | spl9_3 | ~spl9_7),
% 12.62/2.06    inference(avatar_split_clause,[],[f10848,f308,f293,f10853,f10850])).
% 12.62/2.06  fof(f10848,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k2_xboole_0(sK3,k1_tarski(sK2))) | ~r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2))) | (spl9_3 | ~spl9_7)),
% 12.62/2.06    inference(forward_demodulation,[],[f10847,f8394])).
% 12.62/2.06  fof(f8394,plain,(
% 12.62/2.06    ( ! [X18] : (k2_xboole_0(sK3,X18) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X18))) ) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f159,f348])).
% 12.62/2.06  fof(f10847,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k2_xboole_0(sK3,k1_tarski(sK2))) | ~r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | (spl9_3 | ~spl9_7)),
% 12.62/2.06    inference(forward_demodulation,[],[f10833,f8394])).
% 12.62/2.06  fof(f10833,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | ~r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | (spl9_3 | ~spl9_7)),
% 12.62/2.06    inference(resolution,[],[f10819,f294])).
% 12.62/2.06  fof(f294,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | spl9_3),
% 12.62/2.06    inference(avatar_component_clause,[],[f293])).
% 12.62/2.06  fof(f10819,plain,(
% 12.62/2.06    ( ! [X8] : (r1_tarski(sK3,X8) | ~r2_hidden(sK1,X8) | ~r2_hidden(sK0,X8)) ) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f247,f348])).
% 12.62/2.06  fof(f10037,plain,(
% 12.62/2.06    ~spl9_166 | spl9_165 | ~spl9_161),
% 12.62/2.06    inference(avatar_split_clause,[],[f10021,f9979,f10031,f10035])).
% 12.62/2.06  fof(f10031,plain,(
% 12.62/2.06    spl9_165 <=> k1_tarski(sK1) = k4_xboole_0(sK3,k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).
% 12.62/2.06  fof(f9979,plain,(
% 12.62/2.06    spl9_161 <=> r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).
% 12.62/2.06  fof(f10021,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(sK3,k1_tarski(sK0)) | ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1)) | ~spl9_161),
% 12.62/2.06    inference(resolution,[],[f9980,f139])).
% 12.62/2.06  fof(f9980,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0))) | ~spl9_161),
% 12.62/2.06    inference(avatar_component_clause,[],[f9979])).
% 12.62/2.06  fof(f9992,plain,(
% 12.62/2.06    spl9_159 | spl9_162),
% 12.62/2.06    inference(avatar_split_clause,[],[f9989,f9984,f9957])).
% 12.62/2.06  fof(f9984,plain,(
% 12.62/2.06    spl9_162 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).
% 12.62/2.06  fof(f9989,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl9_162),
% 12.62/2.06    inference(resolution,[],[f9985,f154])).
% 12.62/2.06  fof(f9985,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k1_tarski(sK1)) | spl9_162),
% 12.62/2.06    inference(avatar_component_clause,[],[f9984])).
% 12.62/2.06  fof(f9987,plain,(
% 12.62/2.06    ~spl9_162 | ~spl9_154),
% 12.62/2.06    inference(avatar_split_clause,[],[f9972,f9731,f9984])).
% 12.62/2.06  fof(f9731,plain,(
% 12.62/2.06    spl9_154 <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).
% 12.62/2.06  fof(f9972,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k1_tarski(sK1)) | ~spl9_154),
% 12.62/2.06    inference(superposition,[],[f831,f9732])).
% 12.62/2.06  fof(f9732,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | ~spl9_154),
% 12.62/2.06    inference(avatar_component_clause,[],[f9731])).
% 12.62/2.06  fof(f9981,plain,(
% 12.62/2.06    spl9_161 | ~spl9_38 | ~spl9_154),
% 12.62/2.06    inference(avatar_split_clause,[],[f9966,f9731,f6345,f9979])).
% 12.62/2.06  fof(f9966,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK0))) | (~spl9_38 | ~spl9_154)),
% 12.62/2.06    inference(superposition,[],[f7314,f9732])).
% 12.62/2.06  fof(f7314,plain,(
% 12.62/2.06    ( ! [X42] : (r1_tarski(k4_xboole_0(k1_tarski(sK1),X42),k4_xboole_0(sK3,X42))) ) | ~spl9_38),
% 12.62/2.06    inference(resolution,[],[f166,f6346])).
% 12.62/2.06  fof(f9733,plain,(
% 12.62/2.06    spl9_154 | spl9_119),
% 12.62/2.06    inference(avatar_split_clause,[],[f9264,f9178,f9731])).
% 12.62/2.06  fof(f9264,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl9_119),
% 12.62/2.06    inference(resolution,[],[f9261,f154])).
% 12.62/2.06  fof(f9261,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k1_tarski(sK0)) | spl9_119),
% 12.62/2.06    inference(avatar_component_clause,[],[f9178])).
% 12.62/2.06  fof(f9194,plain,(
% 12.62/2.06    spl9_121 | ~spl9_119),
% 12.62/2.06    inference(avatar_split_clause,[],[f9185,f9178,f9192])).
% 12.62/2.06  fof(f9185,plain,(
% 12.62/2.06    sK0 = sK1 | ~spl9_119),
% 12.62/2.06    inference(resolution,[],[f9179,f259])).
% 12.62/2.06  fof(f9179,plain,(
% 12.62/2.06    r2_hidden(sK1,k1_tarski(sK0)) | ~spl9_119),
% 12.62/2.06    inference(avatar_component_clause,[],[f9178])).
% 12.62/2.06  fof(f7909,plain,(
% 12.62/2.06    spl9_104 | ~spl9_103),
% 12.62/2.06    inference(avatar_split_clause,[],[f7900,f7881,f7907])).
% 12.62/2.06  fof(f7907,plain,(
% 12.62/2.06    spl9_104 <=> sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).
% 12.62/2.06  fof(f7881,plain,(
% 12.62/2.06    spl9_103 <=> r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3)),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).
% 12.62/2.06  fof(f7900,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK1)))) | ~spl9_103),
% 12.62/2.06    inference(resolution,[],[f7882,f135])).
% 12.62/2.06  fof(f7882,plain,(
% 12.62/2.06    r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3) | ~spl9_103),
% 12.62/2.06    inference(avatar_component_clause,[],[f7881])).
% 12.62/2.06  fof(f7883,plain,(
% 12.62/2.06    spl9_103 | ~spl9_58),
% 12.62/2.06    inference(avatar_split_clause,[],[f7872,f6747,f7881])).
% 12.62/2.06  fof(f6747,plain,(
% 12.62/2.06    spl9_58 <=> sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 12.62/2.06  fof(f7872,plain,(
% 12.62/2.06    r1_tarski(k4_xboole_0(sK3,k1_tarski(sK1)),sK3) | ~spl9_58),
% 12.62/2.06    inference(superposition,[],[f521,f6748])).
% 12.62/2.06  fof(f6748,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl9_58),
% 12.62/2.06    inference(avatar_component_clause,[],[f6747])).
% 12.62/2.06  fof(f7685,plain,(
% 12.62/2.06    ~spl9_88 | spl9_3),
% 12.62/2.06    inference(avatar_split_clause,[],[f7657,f293,f7683])).
% 12.62/2.06  fof(f7657,plain,(
% 12.62/2.06    ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl9_3),
% 12.62/2.06    inference(resolution,[],[f169,f294])).
% 12.62/2.06  fof(f7643,plain,(
% 12.62/2.06    ~spl9_84 | spl9_85 | ~spl9_79),
% 12.62/2.06    inference(avatar_split_clause,[],[f7622,f7592,f7641,f7638])).
% 12.62/2.06  fof(f7622,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2)) | ~r1_tarski(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK0)) | ~spl9_79),
% 12.62/2.06    inference(resolution,[],[f7593,f139])).
% 12.62/2.06  fof(f7593,plain,(
% 12.62/2.06    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK2))) | ~spl9_79),
% 12.62/2.06    inference(avatar_component_clause,[],[f7592])).
% 12.62/2.06  fof(f7605,plain,(
% 12.62/2.06    spl9_81 | spl9_80),
% 12.62/2.06    inference(avatar_split_clause,[],[f7600,f7596,f7603])).
% 12.62/2.06  fof(f7600,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) | spl9_80),
% 12.62/2.06    inference(resolution,[],[f7597,f154])).
% 12.62/2.06  fof(f7597,plain,(
% 12.62/2.06    ~r2_hidden(sK2,k1_tarski(sK0)) | spl9_80),
% 12.62/2.06    inference(avatar_component_clause,[],[f7596])).
% 12.62/2.06  fof(f7489,plain,(
% 12.62/2.06    spl9_69 | spl9_68),
% 12.62/2.06    inference(avatar_split_clause,[],[f7484,f7480,f7487])).
% 12.62/2.06  fof(f7480,plain,(
% 12.62/2.06    spl9_68 <=> r2_hidden(sK2,k1_tarski(sK1))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 12.62/2.06  fof(f7484,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) | spl9_68),
% 12.62/2.06    inference(resolution,[],[f7481,f154])).
% 12.62/2.06  fof(f7481,plain,(
% 12.62/2.06    ~r2_hidden(sK2,k1_tarski(sK1)) | spl9_68),
% 12.62/2.06    inference(avatar_component_clause,[],[f7480])).
% 12.62/2.06  fof(f7483,plain,(
% 12.62/2.06    ~spl9_68 | ~spl9_65),
% 12.62/2.06    inference(avatar_split_clause,[],[f7472,f7196,f7480])).
% 12.62/2.06  fof(f7472,plain,(
% 12.62/2.06    ~r2_hidden(sK2,k1_tarski(sK1)) | ~spl9_65),
% 12.62/2.06    inference(superposition,[],[f831,f7197])).
% 12.62/2.06  fof(f7204,plain,(
% 12.62/2.06    spl9_66 | spl9_64),
% 12.62/2.06    inference(avatar_split_clause,[],[f7199,f7190,f7202])).
% 12.62/2.06  fof(f7199,plain,(
% 12.62/2.06    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | spl9_64),
% 12.62/2.06    inference(resolution,[],[f7191,f154])).
% 12.62/2.06  fof(f7191,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k1_tarski(sK2)) | spl9_64),
% 12.62/2.06    inference(avatar_component_clause,[],[f7190])).
% 12.62/2.06  fof(f7198,plain,(
% 12.62/2.06    spl9_65 | spl9_63),
% 12.62/2.06    inference(avatar_split_clause,[],[f7193,f7186,f7196])).
% 12.62/2.06  fof(f7193,plain,(
% 12.62/2.06    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | spl9_63),
% 12.62/2.06    inference(resolution,[],[f7187,f154])).
% 12.62/2.06  fof(f7187,plain,(
% 12.62/2.06    ~r2_hidden(sK1,k1_tarski(sK2)) | spl9_63),
% 12.62/2.06    inference(avatar_component_clause,[],[f7186])).
% 12.62/2.06  fof(f7192,plain,(
% 12.62/2.06    ~spl9_64 | ~spl9_39 | ~spl9_62),
% 12.62/2.06    inference(avatar_split_clause,[],[f7183,f7167,f6349,f7190])).
% 12.62/2.06  fof(f7183,plain,(
% 12.62/2.06    ~r2_hidden(sK0,k1_tarski(sK2)) | (~spl9_39 | ~spl9_62)),
% 12.62/2.06    inference(superposition,[],[f6611,f7168])).
% 12.62/2.06  fof(f7179,plain,(
% 12.62/2.06    spl9_62 | spl9_22),
% 12.62/2.06    inference(avatar_split_clause,[],[f7163,f419,f7167])).
% 12.62/2.06  fof(f7163,plain,(
% 12.62/2.06    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) | spl9_22),
% 12.62/2.06    inference(resolution,[],[f154,f6660])).
% 12.62/2.06  fof(f6660,plain,(
% 12.62/2.06    ~r2_hidden(sK2,sK3) | spl9_22),
% 12.62/2.06    inference(avatar_component_clause,[],[f419])).
% 12.62/2.06  fof(f6749,plain,(
% 12.62/2.06    spl9_58 | ~spl9_38),
% 12.62/2.06    inference(avatar_split_clause,[],[f6742,f6345,f6747])).
% 12.62/2.06  fof(f6742,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k1_tarski(sK1))) | ~spl9_38),
% 12.62/2.06    inference(resolution,[],[f6346,f135])).
% 12.62/2.06  fof(f6736,plain,(
% 12.62/2.06    spl9_56 | ~spl9_37),
% 12.62/2.06    inference(avatar_split_clause,[],[f6729,f6341,f6734])).
% 12.62/2.06  fof(f6734,plain,(
% 12.62/2.06    spl9_56 <=> sK3 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 12.62/2.06  fof(f6729,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK0))) | ~spl9_37),
% 12.62/2.06    inference(resolution,[],[f6342,f135])).
% 12.62/2.06  fof(f6722,plain,(
% 12.62/2.06    spl9_19 | ~spl9_39),
% 12.62/2.06    inference(avatar_split_clause,[],[f6610,f6349,f385])).
% 12.62/2.06  fof(f6610,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),sK3) | ~spl9_39),
% 12.62/2.06    inference(resolution,[],[f6350,f134])).
% 12.62/2.06  fof(f6714,plain,(
% 12.62/2.06    spl9_12),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f6712])).
% 12.62/2.06  fof(f6712,plain,(
% 12.62/2.06    $false | spl9_12),
% 12.62/2.06    inference(resolution,[],[f330,f550])).
% 12.62/2.06  fof(f330,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | spl9_12),
% 12.62/2.06    inference(avatar_component_clause,[],[f329])).
% 12.62/2.06  fof(f329,plain,(
% 12.62/2.06    spl9_12 <=> r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 12.62/2.06  fof(f6589,plain,(
% 12.62/2.06    spl9_10),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f6587])).
% 12.62/2.06  fof(f6587,plain,(
% 12.62/2.06    $false | spl9_10),
% 12.62/2.06    inference(resolution,[],[f322,f581])).
% 12.62/2.06  fof(f322,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2)))) | spl9_10),
% 12.62/2.06    inference(avatar_component_clause,[],[f321])).
% 12.62/2.06  fof(f321,plain,(
% 12.62/2.06    spl9_10 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 12.62/2.06  fof(f6455,plain,(
% 12.62/2.06    spl9_39 | ~spl9_18),
% 12.62/2.06    inference(avatar_split_clause,[],[f6454,f377,f6349])).
% 12.62/2.06  fof(f6454,plain,(
% 12.62/2.06    r2_hidden(sK0,sK3) | ~spl9_18),
% 12.62/2.06    inference(trivial_inequality_removal,[],[f6452])).
% 12.62/2.06  fof(f6452,plain,(
% 12.62/2.06    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,sK3) | ~spl9_18),
% 12.62/2.06    inference(superposition,[],[f149,f378])).
% 12.62/2.06  fof(f149,plain,(
% 12.62/2.06    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 12.62/2.06    inference(cnf_transformation,[],[f86])).
% 12.62/2.06  fof(f86,plain,(
% 12.62/2.06    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 12.62/2.06    inference(nnf_transformation,[],[f47])).
% 12.62/2.06  fof(f47,axiom,(
% 12.62/2.06    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 12.62/2.06  fof(f6445,plain,(
% 12.62/2.06    spl9_23 | ~spl9_35),
% 12.62/2.06    inference(avatar_split_clause,[],[f6434,f3386,f424])).
% 12.62/2.06  fof(f6434,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK1),sK3) | ~spl9_35),
% 12.62/2.06    inference(resolution,[],[f3387,f134])).
% 12.62/2.06  fof(f3387,plain,(
% 12.62/2.06    r2_hidden(sK1,sK3) | ~spl9_35),
% 12.62/2.06    inference(avatar_component_clause,[],[f3386])).
% 12.62/2.06  fof(f6354,plain,(
% 12.62/2.06    spl9_39 | ~spl9_7),
% 12.62/2.06    inference(avatar_split_clause,[],[f6333,f308,f6349])).
% 12.62/2.06  fof(f6333,plain,(
% 12.62/2.06    r2_hidden(sK0,sK3) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f2968,f348])).
% 12.62/2.06  fof(f2968,plain,(
% 12.62/2.06    ( ! [X4,X3] : (r2_hidden(X3,k2_xboole_0(k1_tarski(X3),X4))) )),
% 12.62/2.06    inference(resolution,[],[f2961,f550])).
% 12.62/2.06  fof(f6353,plain,(
% 12.62/2.06    spl9_35 | ~spl9_7),
% 12.62/2.06    inference(avatar_split_clause,[],[f6329,f308,f3386])).
% 12.62/2.06  fof(f6329,plain,(
% 12.62/2.06    r2_hidden(sK1,sK3) | ~spl9_7),
% 12.62/2.06    inference(superposition,[],[f2967,f348])).
% 12.62/2.06  fof(f2967,plain,(
% 12.62/2.06    ( ! [X2,X1] : (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X1)))) )),
% 12.62/2.06    inference(resolution,[],[f2961,f521])).
% 12.62/2.06  fof(f6320,plain,(
% 12.62/2.06    spl9_36 | ~spl9_3),
% 12.62/2.06    inference(avatar_split_clause,[],[f6252,f293,f6318])).
% 12.62/2.06  fof(f6252,plain,(
% 12.62/2.06    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)) | ~spl9_3),
% 12.62/2.06    inference(resolution,[],[f135,f343])).
% 12.62/2.06  fof(f2143,plain,(
% 12.62/2.06    spl9_32 | ~spl9_22),
% 12.62/2.06    inference(avatar_split_clause,[],[f2138,f419,f2141])).
% 12.62/2.06  fof(f2138,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK2),sK3) | ~spl9_22),
% 12.62/2.06    inference(resolution,[],[f134,f420])).
% 12.62/2.06  fof(f420,plain,(
% 12.62/2.06    r2_hidden(sK2,sK3) | ~spl9_22),
% 12.62/2.06    inference(avatar_component_clause,[],[f419])).
% 12.62/2.06  fof(f589,plain,(
% 12.62/2.06    spl9_16),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f588])).
% 12.62/2.06  fof(f588,plain,(
% 12.62/2.06    $false | spl9_16),
% 12.62/2.06    inference(subsumption_resolution,[],[f362,f581])).
% 12.62/2.06  fof(f362,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))) | spl9_16),
% 12.62/2.06    inference(avatar_component_clause,[],[f361])).
% 12.62/2.06  fof(f361,plain,(
% 12.62/2.06    spl9_16 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 12.62/2.06  fof(f519,plain,(
% 12.62/2.06    spl9_31 | ~spl9_3),
% 12.62/2.06    inference(avatar_split_clause,[],[f514,f293,f517])).
% 12.62/2.06  fof(f517,plain,(
% 12.62/2.06    spl9_31 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 12.62/2.06  fof(f514,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | ~spl9_3),
% 12.62/2.06    inference(resolution,[],[f148,f343])).
% 12.62/2.06  fof(f148,plain,(
% 12.62/2.06    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 12.62/2.06    inference(cnf_transformation,[],[f85])).
% 12.62/2.06  fof(f510,plain,(
% 12.62/2.06    spl9_29),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f509])).
% 12.62/2.06  fof(f509,plain,(
% 12.62/2.06    $false | spl9_29),
% 12.62/2.06    inference(trivial_inequality_removal,[],[f508])).
% 12.62/2.06  fof(f508,plain,(
% 12.62/2.06    k1_xboole_0 != k1_xboole_0 | spl9_29),
% 12.62/2.06    inference(superposition,[],[f502,f127])).
% 12.62/2.06  fof(f502,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) | spl9_29),
% 12.62/2.06    inference(avatar_component_clause,[],[f501])).
% 12.62/2.06  fof(f501,plain,(
% 12.62/2.06    spl9_29 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 12.62/2.06  fof(f503,plain,(
% 12.62/2.06    ~spl9_29 | spl9_17),
% 12.62/2.06    inference(avatar_split_clause,[],[f497,f366,f501])).
% 12.62/2.06  fof(f366,plain,(
% 12.62/2.06    spl9_17 <=> r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 12.62/2.06  fof(f497,plain,(
% 12.62/2.06    k1_xboole_0 != k4_xboole_0(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) | spl9_17),
% 12.62/2.06    inference(resolution,[],[f147,f367])).
% 12.62/2.06  fof(f367,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) | spl9_17),
% 12.62/2.06    inference(avatar_component_clause,[],[f366])).
% 12.62/2.06  fof(f496,plain,(
% 12.62/2.06    spl9_14),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f495])).
% 12.62/2.06  fof(f495,plain,(
% 12.62/2.06    $false | spl9_14),
% 12.62/2.06    inference(resolution,[],[f338,f118])).
% 12.62/2.06  fof(f338,plain,(
% 12.62/2.06    ~r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) | spl9_14),
% 12.62/2.06    inference(avatar_component_clause,[],[f337])).
% 12.62/2.06  fof(f337,plain,(
% 12.62/2.06    spl9_14 <=> r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 12.62/2.06  fof(f379,plain,(
% 12.62/2.06    spl9_18 | ~spl9_4),
% 12.62/2.06    inference(avatar_split_clause,[],[f373,f296,f377])).
% 12.62/2.06  fof(f373,plain,(
% 12.62/2.06    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3) | ~spl9_4),
% 12.62/2.06    inference(superposition,[],[f127,f350])).
% 12.62/2.06  fof(f370,plain,(
% 12.62/2.06    spl9_1),
% 12.62/2.06    inference(avatar_contradiction_clause,[],[f369])).
% 12.62/2.06  fof(f369,plain,(
% 12.62/2.06    $false | spl9_1),
% 12.62/2.06    inference(resolution,[],[f255,f287])).
% 12.62/2.06  fof(f287,plain,(
% 12.62/2.06    ~r1_tarski(sK3,sK3) | spl9_1),
% 12.62/2.06    inference(avatar_component_clause,[],[f286])).
% 12.62/2.06  fof(f368,plain,(
% 12.62/2.06    ~spl9_17 | spl9_5),
% 12.62/2.06    inference(avatar_split_clause,[],[f364,f301,f366])).
% 12.62/2.06  fof(f301,plain,(
% 12.62/2.06    spl9_5 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 12.62/2.06  fof(f364,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK0))) | spl9_5),
% 12.62/2.06    inference(forward_demodulation,[],[f302,f129])).
% 12.62/2.06  fof(f302,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3)) | spl9_5),
% 12.62/2.06    inference(avatar_component_clause,[],[f301])).
% 12.62/2.06  fof(f363,plain,(
% 12.62/2.06    ~spl9_16 | spl9_8),
% 12.62/2.06    inference(avatar_split_clause,[],[f359,f313,f361])).
% 12.62/2.06  fof(f313,plain,(
% 12.62/2.06    spl9_8 <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3)))),
% 12.62/2.06    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 12.62/2.06  fof(f359,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK1)))) | spl9_8),
% 12.62/2.06    inference(forward_demodulation,[],[f314,f129])).
% 12.62/2.06  fof(f314,plain,(
% 12.62/2.06    ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3))) | spl9_8),
% 12.62/2.06    inference(avatar_component_clause,[],[f313])).
% 12.62/2.06  fof(f352,plain,(
% 12.62/2.06    spl9_3 | spl9_15 | spl9_13 | spl9_11 | spl9_9 | spl9_7 | spl9_6 | spl9_4 | spl9_2),
% 12.62/2.06    inference(avatar_split_clause,[],[f220,f289,f296,f304,f308,f316,f324,f332,f340,f293])).
% 12.62/2.06  fof(f220,plain,(
% 12.62/2.06    sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK3 = k1_tarski(sK2) | sK3 = k1_tarski(sK1) | sK3 = k1_tarski(sK0) | k1_xboole_0 = sK3 | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 12.62/2.06    inference(definition_unfolding,[],[f109,f209,f130,f130,f130,f209])).
% 12.62/2.06  fof(f209,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 12.62/2.06    inference(definition_unfolding,[],[f158,f130])).
% 12.62/2.06  fof(f158,plain,(
% 12.62/2.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 12.62/2.06    inference(cnf_transformation,[],[f31])).
% 12.62/2.06  fof(f31,axiom,(
% 12.62/2.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 12.62/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 12.62/2.06  fof(f109,plain,(
% 12.62/2.06    sK3 = k1_enumset1(sK0,sK1,sK2) | sK3 = k2_tarski(sK0,sK2) | sK3 = k2_tarski(sK1,sK2) | sK3 = k2_tarski(sK0,sK1) | sK3 = k1_tarski(sK2) | sK3 = k1_tarski(sK1) | sK3 = k1_tarski(sK0) | k1_xboole_0 = sK3 | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 12.62/2.06    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  % (10050)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.21/2.07  fof(f74,plain,(
% 13.21/2.07    ((sK3 != k1_enumset1(sK0,sK1,sK2) & sK3 != k2_tarski(sK0,sK2) & sK3 != k2_tarski(sK1,sK2) & sK3 != k2_tarski(sK0,sK1) & sK3 != k1_tarski(sK2) & sK3 != k1_tarski(sK1) & sK3 != k1_tarski(sK0) & k1_xboole_0 != sK3) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))) & (sK3 = k1_enumset1(sK0,sK1,sK2) | sK3 = k2_tarski(sK0,sK2) | sK3 = k2_tarski(sK1,sK2) | sK3 = k2_tarski(sK0,sK1) | sK3 = k1_tarski(sK2) | sK3 = k1_tarski(sK1) | sK3 = k1_tarski(sK0) | k1_xboole_0 = sK3 | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)))),
% 13.21/2.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f72,f73])).
% 13.21/2.07  fof(f73,plain,(
% 13.21/2.07    ? [X0,X1,X2,X3] : (((k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | r1_tarski(X3,k1_enumset1(X0,X1,X2)))) => (((sK3 != k1_enumset1(sK0,sK1,sK2) & sK3 != k2_tarski(sK0,sK2) & sK3 != k2_tarski(sK1,sK2) & sK3 != k2_tarski(sK0,sK1) & sK3 != k1_tarski(sK2) & sK3 != k1_tarski(sK1) & sK3 != k1_tarski(sK0) & k1_xboole_0 != sK3) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))) & (sK3 = k1_enumset1(sK0,sK1,sK2) | sK3 = k2_tarski(sK0,sK2) | sK3 = k2_tarski(sK1,sK2) | sK3 = k2_tarski(sK0,sK1) | sK3 = k1_tarski(sK2) | sK3 = k1_tarski(sK1) | sK3 = k1_tarski(sK0) | k1_xboole_0 = sK3 | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))))),
% 13.21/2.07    introduced(choice_axiom,[])).
% 13.21/2.07  fof(f72,plain,(
% 13.21/2.07    ? [X0,X1,X2,X3] : (((k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 13.21/2.07    inference(flattening,[],[f71])).
% 13.21/2.07  fof(f71,plain,(
% 13.21/2.07    ? [X0,X1,X2,X3] : (((k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 13.21/2.07    inference(nnf_transformation,[],[f52])).
% 13.21/2.07  fof(f52,plain,(
% 13.21/2.07    ? [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <~> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 13.21/2.07    inference(ennf_transformation,[],[f50])).
% 13.21/2.07  fof(f50,negated_conjecture,(
% 13.21/2.07    ~! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 13.21/2.07    inference(negated_conjecture,[],[f49])).
% 13.21/2.07  fof(f49,conjecture,(
% 13.21/2.07    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 13.21/2.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 13.21/2.07  fof(f342,plain,(
% 13.21/2.07    ~spl9_14 | ~spl9_15),
% 13.21/2.07    inference(avatar_split_clause,[],[f335,f340,f337])).
% 13.21/2.07  fof(f335,plain,(
% 13.21/2.07    k1_xboole_0 != sK3 | ~r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(inner_rewriting,[],[f219])).
% 13.21/2.07  fof(f219,plain,(
% 13.21/2.07    k1_xboole_0 != sK3 | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f110,f209])).
% 13.21/2.07  fof(f110,plain,(
% 13.21/2.07    k1_xboole_0 != sK3 | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f334,plain,(
% 13.21/2.07    ~spl9_12 | ~spl9_13),
% 13.21/2.07    inference(avatar_split_clause,[],[f327,f332,f329])).
% 13.21/2.07  fof(f327,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK0) | ~r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(inner_rewriting,[],[f218])).
% 13.21/2.07  fof(f218,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK0) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f111,f209])).
% 13.21/2.07  fof(f111,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK0) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f326,plain,(
% 13.21/2.07    ~spl9_10 | ~spl9_11),
% 13.21/2.07    inference(avatar_split_clause,[],[f319,f324,f321])).
% 13.21/2.07  fof(f319,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK1) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k1_tarski(sK2))))),
% 13.21/2.07    inference(inner_rewriting,[],[f217])).
% 13.21/2.07  fof(f217,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK1) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f112,f209])).
% 13.21/2.07  fof(f112,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK1) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f318,plain,(
% 13.21/2.07    ~spl9_8 | ~spl9_9),
% 13.21/2.07    inference(avatar_split_clause,[],[f311,f316,f313])).
% 13.21/2.07  fof(f311,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK2) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3)))),
% 13.21/2.07    inference(inner_rewriting,[],[f216])).
% 13.21/2.07  fof(f216,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK2) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f113,f209])).
% 13.21/2.07  fof(f113,plain,(
% 13.21/2.07    sK3 != k1_tarski(sK2) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f310,plain,(
% 13.21/2.07    ~spl9_3 | ~spl9_7),
% 13.21/2.07    inference(avatar_split_clause,[],[f215,f308,f293])).
% 13.21/2.07  fof(f215,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f114,f130,f209])).
% 13.21/2.07  fof(f114,plain,(
% 13.21/2.07    sK3 != k2_tarski(sK0,sK1) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f306,plain,(
% 13.21/2.07    ~spl9_5 | ~spl9_6),
% 13.21/2.07    inference(avatar_split_clause,[],[f299,f304,f301])).
% 13.21/2.07  fof(f299,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3))),
% 13.21/2.07    inference(inner_rewriting,[],[f214])).
% 13.21/2.07  fof(f214,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f115,f130,f209])).
% 13.21/2.07  fof(f115,plain,(
% 13.21/2.07    sK3 != k2_tarski(sK1,sK2) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f298,plain,(
% 13.21/2.07    ~spl9_3 | ~spl9_4),
% 13.21/2.07    inference(avatar_split_clause,[],[f213,f296,f293])).
% 13.21/2.07  fof(f213,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f116,f130,f209])).
% 13.21/2.07  fof(f116,plain,(
% 13.21/2.07    sK3 != k2_tarski(sK0,sK2) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  fof(f291,plain,(
% 13.21/2.07    ~spl9_1 | ~spl9_2),
% 13.21/2.07    inference(avatar_split_clause,[],[f284,f289,f286])).
% 13.21/2.07  fof(f284,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~r1_tarski(sK3,sK3)),
% 13.21/2.07    inference(inner_rewriting,[],[f212])).
% 13.21/2.07  fof(f212,plain,(
% 13.21/2.07    sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 13.21/2.07    inference(definition_unfolding,[],[f117,f209,f209])).
% 13.21/2.07  fof(f117,plain,(
% 13.21/2.07    sK3 != k1_enumset1(sK0,sK1,sK2) | ~r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2))),
% 13.21/2.07    inference(cnf_transformation,[],[f74])).
% 13.21/2.07  % SZS output end Proof for theBenchmark
% 13.21/2.07  % (9794)------------------------------
% 13.21/2.07  % (9794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.21/2.07  % (9794)Termination reason: Refutation
% 13.21/2.07  
% 13.21/2.07  % (9794)Memory used [KB]: 21875
% 13.21/2.07  % (9794)Time elapsed: 1.649 s
% 13.21/2.07  % (9794)------------------------------
% 13.21/2.07  % (9794)------------------------------
% 13.21/2.07  % (10052)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.21/2.08  % (9774)Success in time 1.729 s
%------------------------------------------------------------------------------
