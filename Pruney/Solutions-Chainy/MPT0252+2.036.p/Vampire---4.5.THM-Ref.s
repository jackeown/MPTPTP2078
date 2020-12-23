%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:55 EST 2020

% Result     : Theorem 9.34s
% Output     : Refutation 9.34s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 154 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  229 ( 403 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f79,f95,f113,f121,f125,f129,f168,f294,f303,f318,f1462,f3648,f4377,f4394,f4950,f5255,f7127])).

fof(f7127,plain,
    ( ~ spl3_7
    | spl3_32
    | ~ spl3_126 ),
    inference(avatar_contradiction_clause,[],[f7126])).

fof(f7126,plain,
    ( $false
    | ~ spl3_7
    | spl3_32
    | ~ spl3_126 ),
    inference(subsumption_resolution,[],[f283,f7048])).

fof(f7048,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl3_7
    | ~ spl3_126 ),
    inference(superposition,[],[f94,f5254])).

fof(f5254,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl3_126 ),
    inference(avatar_component_clause,[],[f5253])).

fof(f5253,plain,
    ( spl3_126
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).

fof(f94,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f283,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_32
  <=> r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f5255,plain,
    ( spl3_126
    | ~ spl3_11
    | ~ spl3_114 ),
    inference(avatar_split_clause,[],[f5207,f4948,f111,f5253])).

fof(f111,plain,
    ( spl3_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f4948,plain,
    ( spl3_114
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f5207,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl3_11
    | ~ spl3_114 ),
    inference(superposition,[],[f4949,f112])).

fof(f112,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f4949,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ spl3_114 ),
    inference(avatar_component_clause,[],[f4948])).

fof(f4950,plain,
    ( spl3_114
    | ~ spl3_11
    | ~ spl3_101 ),
    inference(avatar_split_clause,[],[f4653,f3646,f111,f4948])).

fof(f3646,plain,
    ( spl3_101
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f4653,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ spl3_11
    | ~ spl3_101 ),
    inference(superposition,[],[f112,f3647])).

fof(f3647,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f3646])).

fof(f4394,plain,
    ( ~ spl3_32
    | ~ spl3_2
    | ~ spl3_15
    | spl3_33 ),
    inference(avatar_split_clause,[],[f289,f285,f127,f72,f281])).

fof(f72,plain,
    ( spl3_2
  <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f285,plain,
    ( spl3_33
  <=> sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f289,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl3_2
    | ~ spl3_15
    | spl3_33 ),
    inference(unit_resulting_resolution,[],[f74,f286,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f286,plain,
    ( sK2 != k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f285])).

fof(f74,plain,
    ( r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f4377,plain,
    ( spl3_1
    | ~ spl3_33
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f4376])).

fof(f4376,plain,
    ( $false
    | spl3_1
    | ~ spl3_33
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f69,f4364])).

fof(f4364,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_33
    | ~ spl3_37 ),
    inference(superposition,[],[f317,f287])).

fof(f287,plain,
    ( sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f285])).

fof(f317,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl3_37
  <=> ! [X1,X0,X2] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f69,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3648,plain,
    ( spl3_101
    | ~ spl3_15
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1471,f1460,f127,f3646])).

fof(f1460,plain,
    ( spl3_80
  <=> ! [X1,X0] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f1471,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_15
    | ~ spl3_80 ),
    inference(unit_resulting_resolution,[],[f1461,f1461,f128])).

fof(f1461,plain,
    ( ! [X0,X1] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f1462,plain,
    ( spl3_80
    | ~ spl3_20
    | ~ spl3_34
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f304,f301,f292,f166,f1460])).

fof(f166,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f292,plain,
    ( spl3_34
  <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f301,plain,
    ( spl3_35
  <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f304,plain,
    ( ! [X0,X1] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))
    | ~ spl3_20
    | ~ spl3_34
    | ~ spl3_35 ),
    inference(unit_resulting_resolution,[],[f293,f302,f167])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f302,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f301])).

fof(f293,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f318,plain,
    ( spl3_37
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f134,f119,f93,f316])).

fof(f119,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f134,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f94,f120])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f303,plain,
    ( spl3_35
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f143,f123,f77,f301])).

fof(f77,plain,
    ( spl3_3
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f123,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f143,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0))
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f78,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f78,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f294,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f133,f119,f77,f292])).

fof(f133,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f78,f120])).

fof(f168,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f54,f166])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f129,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f49,f127])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f53,f123])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f95,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f64,f77])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f70,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (12110)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.46  % (12118)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (12101)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (12109)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (12109)Refutation not found, incomplete strategy% (12109)------------------------------
% 0.21/0.52  % (12109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12109)Memory used [KB]: 10618
% 0.21/0.52  % (12109)Time elapsed: 0.116 s
% 0.21/0.52  % (12109)------------------------------
% 0.21/0.52  % (12109)------------------------------
% 0.21/0.52  % (12097)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12098)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (12098)Refutation not found, incomplete strategy% (12098)------------------------------
% 0.21/0.52  % (12098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12098)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12098)Memory used [KB]: 1663
% 0.21/0.52  % (12098)Time elapsed: 0.114 s
% 0.21/0.52  % (12098)------------------------------
% 0.21/0.52  % (12098)------------------------------
% 0.21/0.52  % (12119)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (12115)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (12115)Refutation not found, incomplete strategy% (12115)------------------------------
% 0.21/0.52  % (12115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12115)Memory used [KB]: 1663
% 0.21/0.52  % (12115)Time elapsed: 0.122 s
% 0.21/0.52  % (12115)------------------------------
% 0.21/0.52  % (12115)------------------------------
% 0.21/0.53  % (12099)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12124)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (12100)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (12107)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (12104)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (12111)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (12111)Refutation not found, incomplete strategy% (12111)------------------------------
% 0.21/0.53  % (12111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12111)Memory used [KB]: 1663
% 0.21/0.53  % (12111)Time elapsed: 0.093 s
% 0.21/0.53  % (12111)------------------------------
% 0.21/0.53  % (12111)------------------------------
% 0.21/0.53  % (12116)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (12117)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (12112)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (12102)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (12121)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (12103)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12121)Refutation not found, incomplete strategy% (12121)------------------------------
% 0.21/0.54  % (12121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12121)Memory used [KB]: 10746
% 0.21/0.54  % (12121)Time elapsed: 0.140 s
% 0.21/0.54  % (12121)------------------------------
% 0.21/0.54  % (12121)------------------------------
% 0.21/0.54  % (12123)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (12123)Refutation not found, incomplete strategy% (12123)------------------------------
% 0.21/0.54  % (12123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12123)Memory used [KB]: 6140
% 0.21/0.54  % (12123)Time elapsed: 0.142 s
% 0.21/0.54  % (12123)------------------------------
% 0.21/0.54  % (12123)------------------------------
% 0.21/0.54  % (12108)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (12106)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (12113)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (12107)Refutation not found, incomplete strategy% (12107)------------------------------
% 0.21/0.54  % (12107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12105)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (12107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12107)Memory used [KB]: 10874
% 0.21/0.54  % (12107)Time elapsed: 0.134 s
% 0.21/0.54  % (12107)------------------------------
% 0.21/0.54  % (12107)------------------------------
% 0.21/0.54  % (12126)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (12108)Refutation not found, incomplete strategy% (12108)------------------------------
% 0.21/0.54  % (12108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12126)Refutation not found, incomplete strategy% (12126)------------------------------
% 0.21/0.54  % (12126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12113)Refutation not found, incomplete strategy% (12113)------------------------------
% 0.21/0.54  % (12113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (12120)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (12114)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (12124)Refutation not found, incomplete strategy% (12124)------------------------------
% 0.21/0.55  % (12124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12124)Memory used [KB]: 6140
% 0.21/0.55  % (12124)Time elapsed: 0.105 s
% 0.21/0.55  % (12124)------------------------------
% 0.21/0.55  % (12124)------------------------------
% 0.21/0.55  % (12114)Refutation not found, incomplete strategy% (12114)------------------------------
% 0.21/0.55  % (12114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12114)Memory used [KB]: 1791
% 0.21/0.55  % (12114)Time elapsed: 0.151 s
% 0.21/0.55  % (12114)------------------------------
% 0.21/0.55  % (12114)------------------------------
% 0.21/0.55  % (12122)Refutation not found, incomplete strategy% (12122)------------------------------
% 0.21/0.55  % (12122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12122)Memory used [KB]: 6140
% 0.21/0.55  % (12122)Time elapsed: 0.150 s
% 0.21/0.55  % (12122)------------------------------
% 0.21/0.55  % (12122)------------------------------
% 0.21/0.55  % (12126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12126)Memory used [KB]: 1663
% 0.21/0.55  % (12126)Time elapsed: 0.142 s
% 0.21/0.55  % (12126)------------------------------
% 0.21/0.55  % (12126)------------------------------
% 0.21/0.55  % (12125)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (12125)Refutation not found, incomplete strategy% (12125)------------------------------
% 0.21/0.55  % (12125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12125)Memory used [KB]: 10874
% 0.21/0.55  % (12125)Time elapsed: 0.148 s
% 0.21/0.55  % (12125)------------------------------
% 0.21/0.55  % (12125)------------------------------
% 0.21/0.55  % (12108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12108)Memory used [KB]: 6268
% 0.21/0.55  % (12108)Time elapsed: 0.142 s
% 0.21/0.55  % (12108)------------------------------
% 0.21/0.55  % (12108)------------------------------
% 0.21/0.56  % (12113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12113)Memory used [KB]: 10618
% 0.21/0.56  % (12113)Time elapsed: 0.143 s
% 0.21/0.56  % (12113)------------------------------
% 0.21/0.56  % (12113)------------------------------
% 2.14/0.65  % (12127)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.66  % (12130)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.14/0.66  % (12130)Refutation not found, incomplete strategy% (12130)------------------------------
% 2.14/0.66  % (12130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (12130)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.66  
% 2.14/0.66  % (12130)Memory used [KB]: 10618
% 2.14/0.66  % (12130)Time elapsed: 0.095 s
% 2.14/0.66  % (12130)------------------------------
% 2.14/0.66  % (12130)------------------------------
% 2.14/0.66  % (12139)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.14/0.66  % (12099)Refutation not found, incomplete strategy% (12099)------------------------------
% 2.14/0.66  % (12099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (12099)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.66  
% 2.14/0.66  % (12099)Memory used [KB]: 6268
% 2.14/0.66  % (12099)Time elapsed: 0.258 s
% 2.14/0.66  % (12099)------------------------------
% 2.14/0.66  % (12099)------------------------------
% 2.14/0.67  % (12139)Refutation not found, incomplete strategy% (12139)------------------------------
% 2.14/0.67  % (12139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (12134)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.14/0.67  % (12100)Refutation not found, incomplete strategy% (12100)------------------------------
% 2.14/0.67  % (12100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (12129)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.14/0.67  % (12135)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.14/0.67  % (12132)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.14/0.67  % (12138)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.14/0.67  % (12132)Refutation not found, incomplete strategy% (12132)------------------------------
% 2.14/0.67  % (12132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (12132)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.67  
% 2.14/0.67  % (12132)Memory used [KB]: 1791
% 2.14/0.67  % (12132)Time elapsed: 0.106 s
% 2.14/0.67  % (12132)------------------------------
% 2.14/0.67  % (12132)------------------------------
% 2.14/0.67  % (12133)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.14/0.67  % (12138)Refutation not found, incomplete strategy% (12138)------------------------------
% 2.14/0.67  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (12138)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.67  
% 2.14/0.67  % (12138)Memory used [KB]: 10746
% 2.14/0.67  % (12138)Time elapsed: 0.095 s
% 2.14/0.67  % (12138)------------------------------
% 2.14/0.67  % (12138)------------------------------
% 2.14/0.67  % (12133)Refutation not found, incomplete strategy% (12133)------------------------------
% 2.14/0.67  % (12133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (12133)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.67  
% 2.14/0.67  % (12133)Memory used [KB]: 10618
% 2.14/0.67  % (12133)Time elapsed: 0.105 s
% 2.14/0.67  % (12133)------------------------------
% 2.14/0.67  % (12133)------------------------------
% 2.14/0.68  % (12131)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.14/0.68  % (12137)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.14/0.68  % (12129)Refutation not found, incomplete strategy% (12129)------------------------------
% 2.14/0.68  % (12129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (12131)Refutation not found, incomplete strategy% (12131)------------------------------
% 2.14/0.68  % (12131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (12131)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (12131)Memory used [KB]: 10746
% 2.14/0.68  % (12131)Time elapsed: 0.115 s
% 2.14/0.68  % (12131)------------------------------
% 2.14/0.68  % (12131)------------------------------
% 2.14/0.68  % (12097)Refutation not found, incomplete strategy% (12097)------------------------------
% 2.14/0.68  % (12097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (12097)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (12097)Memory used [KB]: 1791
% 2.14/0.68  % (12097)Time elapsed: 0.277 s
% 2.14/0.68  % (12097)------------------------------
% 2.14/0.68  % (12097)------------------------------
% 2.14/0.68  % (12100)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  % (12139)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (12139)Memory used [KB]: 1791
% 2.14/0.68  % (12139)Time elapsed: 0.089 s
% 2.14/0.68  % (12139)------------------------------
% 2.14/0.68  % (12139)------------------------------
% 2.14/0.68  
% 2.14/0.68  % (12100)Memory used [KB]: 6140
% 2.14/0.68  % (12100)Time elapsed: 0.268 s
% 2.14/0.68  % (12100)------------------------------
% 2.14/0.68  % (12100)------------------------------
% 2.14/0.68  % (12129)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (12129)Memory used [KB]: 6268
% 2.14/0.68  % (12129)Time elapsed: 0.110 s
% 2.14/0.68  % (12129)------------------------------
% 2.14/0.68  % (12129)------------------------------
% 2.14/0.68  % (12105)Refutation not found, incomplete strategy% (12105)------------------------------
% 2.14/0.68  % (12105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (12140)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.14/0.68  % (12105)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (12105)Memory used [KB]: 6140
% 2.14/0.68  % (12105)Time elapsed: 0.279 s
% 2.14/0.68  % (12105)------------------------------
% 2.14/0.68  % (12105)------------------------------
% 2.14/0.69  % (12136)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.14/0.69  % (12140)Refutation not found, incomplete strategy% (12140)------------------------------
% 2.14/0.69  % (12140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (12140)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.69  
% 2.14/0.69  % (12140)Memory used [KB]: 10618
% 2.14/0.69  % (12140)Time elapsed: 0.110 s
% 2.14/0.69  % (12140)------------------------------
% 2.14/0.69  % (12140)------------------------------
% 2.14/0.69  % (12136)Refutation not found, incomplete strategy% (12136)------------------------------
% 2.14/0.69  % (12136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (12136)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.69  
% 2.14/0.69  % (12136)Memory used [KB]: 10746
% 2.14/0.69  % (12136)Time elapsed: 0.121 s
% 2.14/0.69  % (12136)------------------------------
% 2.14/0.69  % (12136)------------------------------
% 2.14/0.69  % (12128)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.14/0.70  % (12112)Refutation not found, incomplete strategy% (12112)------------------------------
% 2.14/0.70  % (12112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.70  % (12112)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.70  
% 2.14/0.70  % (12112)Memory used [KB]: 6140
% 2.14/0.70  % (12112)Time elapsed: 0.290 s
% 2.14/0.70  % (12112)------------------------------
% 2.14/0.70  % (12112)------------------------------
% 3.14/0.78  % (12144)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.14/0.79  % (12147)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.14/0.79  % (12143)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.14/0.79  % (12145)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.14/0.79  % (12142)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.14/0.80  % (12141)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.14/0.81  % (12146)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.14/0.81  % (12146)Refutation not found, incomplete strategy% (12146)------------------------------
% 3.14/0.81  % (12146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.81  % (12146)Termination reason: Refutation not found, incomplete strategy
% 3.14/0.81  
% 3.14/0.81  % (12146)Memory used [KB]: 1663
% 3.14/0.81  % (12146)Time elapsed: 0.090 s
% 3.14/0.81  % (12146)------------------------------
% 3.14/0.81  % (12146)------------------------------
% 3.14/0.82  % (12135)Refutation not found, incomplete strategy% (12135)------------------------------
% 3.14/0.82  % (12135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.82  % (12135)Termination reason: Refutation not found, incomplete strategy
% 3.14/0.82  
% 3.14/0.82  % (12135)Memory used [KB]: 6140
% 3.14/0.82  % (12135)Time elapsed: 0.251 s
% 3.14/0.82  % (12135)------------------------------
% 3.14/0.82  % (12135)------------------------------
% 3.91/0.90  % (12142)Refutation not found, incomplete strategy% (12142)------------------------------
% 3.91/0.90  % (12142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (12141)Refutation not found, incomplete strategy% (12141)------------------------------
% 3.91/0.91  % (12141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.92  % (12142)Termination reason: Refutation not found, incomplete strategy
% 3.91/0.92  
% 3.91/0.92  % (12142)Memory used [KB]: 6140
% 3.91/0.92  % (12142)Time elapsed: 0.211 s
% 3.91/0.92  % (12142)------------------------------
% 3.91/0.92  % (12142)------------------------------
% 3.91/0.92  % (12141)Termination reason: Refutation not found, incomplete strategy
% 3.91/0.92  
% 3.91/0.92  % (12141)Memory used [KB]: 6268
% 3.91/0.92  % (12141)Time elapsed: 0.213 s
% 3.91/0.92  % (12141)------------------------------
% 3.91/0.92  % (12141)------------------------------
% 4.29/0.96  % (12103)Time limit reached!
% 4.29/0.96  % (12103)------------------------------
% 4.29/0.96  % (12103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.98  % (12103)Termination reason: Time limit
% 4.29/0.98  
% 4.29/0.98  % (12103)Memory used [KB]: 16247
% 4.29/0.98  % (12103)Time elapsed: 0.527 s
% 4.29/0.98  % (12103)------------------------------
% 4.29/0.98  % (12103)------------------------------
% 4.78/1.00  % (12104)Time limit reached!
% 4.78/1.00  % (12104)------------------------------
% 4.78/1.00  % (12104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.78/1.00  % (12104)Termination reason: Time limit
% 4.78/1.00  % (12104)Termination phase: Saturation
% 4.78/1.00  
% 4.78/1.00  % (12104)Memory used [KB]: 19957
% 4.78/1.00  % (12104)Time elapsed: 0.600 s
% 4.78/1.00  % (12104)------------------------------
% 4.78/1.00  % (12104)------------------------------
% 5.72/1.13  % (12147)Time limit reached!
% 5.72/1.13  % (12147)------------------------------
% 5.72/1.13  % (12147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.13  % (12147)Termination reason: Time limit
% 5.72/1.13  
% 5.72/1.13  % (12147)Memory used [KB]: 10618
% 5.72/1.13  % (12147)Time elapsed: 0.413 s
% 5.72/1.13  % (12147)------------------------------
% 5.72/1.13  % (12147)------------------------------
% 5.72/1.13  % (12144)Time limit reached!
% 5.72/1.13  % (12144)------------------------------
% 5.72/1.13  % (12144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.72/1.13  % (12144)Termination reason: Time limit
% 5.72/1.13  % (12144)Termination phase: Saturation
% 5.72/1.13  
% 5.72/1.13  % (12144)Memory used [KB]: 16247
% 5.72/1.13  % (12144)Time elapsed: 0.400 s
% 5.72/1.13  % (12144)------------------------------
% 5.72/1.13  % (12144)------------------------------
% 6.95/1.24  % (12143)Time limit reached!
% 6.95/1.24  % (12143)------------------------------
% 6.95/1.24  % (12143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.24  % (12143)Termination reason: Time limit
% 6.95/1.24  % (12143)Termination phase: Saturation
% 6.95/1.24  
% 6.95/1.24  % (12143)Memory used [KB]: 16502
% 6.95/1.24  % (12143)Time elapsed: 0.500 s
% 6.95/1.24  % (12143)------------------------------
% 6.95/1.24  % (12143)------------------------------
% 9.34/1.60  % (12127)Refutation found. Thanks to Tanya!
% 9.34/1.60  % SZS status Theorem for theBenchmark
% 9.34/1.61  % SZS output start Proof for theBenchmark
% 9.34/1.61  fof(f7132,plain,(
% 9.34/1.61    $false),
% 9.34/1.61    inference(avatar_sat_refutation,[],[f70,f75,f79,f95,f113,f121,f125,f129,f168,f294,f303,f318,f1462,f3648,f4377,f4394,f4950,f5255,f7127])).
% 9.34/1.61  fof(f7127,plain,(
% 9.34/1.61    ~spl3_7 | spl3_32 | ~spl3_126),
% 9.34/1.61    inference(avatar_contradiction_clause,[],[f7126])).
% 9.34/1.61  fof(f7126,plain,(
% 9.34/1.61    $false | (~spl3_7 | spl3_32 | ~spl3_126)),
% 9.34/1.61    inference(subsumption_resolution,[],[f283,f7048])).
% 9.34/1.61  fof(f7048,plain,(
% 9.34/1.61    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | (~spl3_7 | ~spl3_126)),
% 9.34/1.61    inference(superposition,[],[f94,f5254])).
% 9.34/1.61  fof(f5254,plain,(
% 9.34/1.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl3_126),
% 9.34/1.61    inference(avatar_component_clause,[],[f5253])).
% 9.34/1.61  fof(f5253,plain,(
% 9.34/1.61    spl3_126 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).
% 9.34/1.61  fof(f94,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_7),
% 9.34/1.61    inference(avatar_component_clause,[],[f93])).
% 9.34/1.61  fof(f93,plain,(
% 9.34/1.61    spl3_7 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 9.34/1.61  fof(f283,plain,(
% 9.34/1.61    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_32),
% 9.34/1.61    inference(avatar_component_clause,[],[f281])).
% 9.34/1.61  fof(f281,plain,(
% 9.34/1.61    spl3_32 <=> r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 9.34/1.61  fof(f5255,plain,(
% 9.34/1.61    spl3_126 | ~spl3_11 | ~spl3_114),
% 9.34/1.61    inference(avatar_split_clause,[],[f5207,f4948,f111,f5253])).
% 9.34/1.61  fof(f111,plain,(
% 9.34/1.61    spl3_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 9.34/1.61  fof(f4948,plain,(
% 9.34/1.61    spl3_114 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 9.34/1.61  fof(f5207,plain,(
% 9.34/1.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl3_11 | ~spl3_114)),
% 9.34/1.61    inference(superposition,[],[f4949,f112])).
% 9.34/1.61  fof(f112,plain,(
% 9.34/1.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl3_11),
% 9.34/1.61    inference(avatar_component_clause,[],[f111])).
% 9.34/1.61  fof(f4949,plain,(
% 9.34/1.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))) ) | ~spl3_114),
% 9.34/1.61    inference(avatar_component_clause,[],[f4948])).
% 9.34/1.61  fof(f4950,plain,(
% 9.34/1.61    spl3_114 | ~spl3_11 | ~spl3_101),
% 9.34/1.61    inference(avatar_split_clause,[],[f4653,f3646,f111,f4948])).
% 9.34/1.61  fof(f3646,plain,(
% 9.34/1.61    spl3_101 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 9.34/1.61  fof(f4653,plain,(
% 9.34/1.61    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))) ) | (~spl3_11 | ~spl3_101)),
% 9.34/1.61    inference(superposition,[],[f112,f3647])).
% 9.34/1.61  fof(f3647,plain,(
% 9.34/1.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_101),
% 9.34/1.61    inference(avatar_component_clause,[],[f3646])).
% 9.34/1.61  fof(f4394,plain,(
% 9.34/1.61    ~spl3_32 | ~spl3_2 | ~spl3_15 | spl3_33),
% 9.34/1.61    inference(avatar_split_clause,[],[f289,f285,f127,f72,f281])).
% 9.34/1.61  fof(f72,plain,(
% 9.34/1.61    spl3_2 <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 9.34/1.61  fof(f127,plain,(
% 9.34/1.61    spl3_15 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 9.34/1.61  fof(f285,plain,(
% 9.34/1.61    spl3_33 <=> sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 9.34/1.61  fof(f289,plain,(
% 9.34/1.61    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | (~spl3_2 | ~spl3_15 | spl3_33)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f74,f286,f128])).
% 9.34/1.61  fof(f128,plain,(
% 9.34/1.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_15),
% 9.34/1.61    inference(avatar_component_clause,[],[f127])).
% 9.34/1.61  fof(f286,plain,(
% 9.34/1.61    sK2 != k2_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_33),
% 9.34/1.61    inference(avatar_component_clause,[],[f285])).
% 9.34/1.61  fof(f74,plain,(
% 9.34/1.61    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | ~spl3_2),
% 9.34/1.61    inference(avatar_component_clause,[],[f72])).
% 9.34/1.61  fof(f4377,plain,(
% 9.34/1.61    spl3_1 | ~spl3_33 | ~spl3_37),
% 9.34/1.61    inference(avatar_contradiction_clause,[],[f4376])).
% 9.34/1.61  fof(f4376,plain,(
% 9.34/1.61    $false | (spl3_1 | ~spl3_33 | ~spl3_37)),
% 9.34/1.61    inference(subsumption_resolution,[],[f69,f4364])).
% 9.34/1.61  fof(f4364,plain,(
% 9.34/1.61    r2_hidden(sK0,sK2) | (~spl3_33 | ~spl3_37)),
% 9.34/1.61    inference(superposition,[],[f317,f287])).
% 9.34/1.61  fof(f287,plain,(
% 9.34/1.61    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_33),
% 9.34/1.61    inference(avatar_component_clause,[],[f285])).
% 9.34/1.61  fof(f317,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl3_37),
% 9.34/1.61    inference(avatar_component_clause,[],[f316])).
% 9.34/1.61  fof(f316,plain,(
% 9.34/1.61    spl3_37 <=> ! [X1,X0,X2] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 9.34/1.61  fof(f69,plain,(
% 9.34/1.61    ~r2_hidden(sK0,sK2) | spl3_1),
% 9.34/1.61    inference(avatar_component_clause,[],[f67])).
% 9.34/1.61  fof(f67,plain,(
% 9.34/1.61    spl3_1 <=> r2_hidden(sK0,sK2)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 9.34/1.61  fof(f3648,plain,(
% 9.34/1.61    spl3_101 | ~spl3_15 | ~spl3_80),
% 9.34/1.61    inference(avatar_split_clause,[],[f1471,f1460,f127,f3646])).
% 9.34/1.61  fof(f1460,plain,(
% 9.34/1.61    spl3_80 <=> ! [X1,X0] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 9.34/1.61  fof(f1471,plain,(
% 9.34/1.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | (~spl3_15 | ~spl3_80)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f1461,f1461,f128])).
% 9.34/1.61  fof(f1461,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))) ) | ~spl3_80),
% 9.34/1.61    inference(avatar_component_clause,[],[f1460])).
% 9.34/1.61  fof(f1462,plain,(
% 9.34/1.61    spl3_80 | ~spl3_20 | ~spl3_34 | ~spl3_35),
% 9.34/1.61    inference(avatar_split_clause,[],[f304,f301,f292,f166,f1460])).
% 9.34/1.61  fof(f166,plain,(
% 9.34/1.61    spl3_20 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 9.34/1.61  fof(f292,plain,(
% 9.34/1.61    spl3_34 <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X0,X1))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 9.34/1.61  fof(f301,plain,(
% 9.34/1.61    spl3_35 <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X1,X0))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 9.34/1.61  fof(f304,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))) ) | (~spl3_20 | ~spl3_34 | ~spl3_35)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f293,f302,f167])).
% 9.34/1.61  fof(f167,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) ) | ~spl3_20),
% 9.34/1.61    inference(avatar_component_clause,[],[f166])).
% 9.34/1.61  fof(f302,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) ) | ~spl3_35),
% 9.34/1.61    inference(avatar_component_clause,[],[f301])).
% 9.34/1.61  fof(f293,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) ) | ~spl3_34),
% 9.34/1.61    inference(avatar_component_clause,[],[f292])).
% 9.34/1.61  fof(f318,plain,(
% 9.34/1.61    spl3_37 | ~spl3_7 | ~spl3_13),
% 9.34/1.61    inference(avatar_split_clause,[],[f134,f119,f93,f316])).
% 9.34/1.61  fof(f119,plain,(
% 9.34/1.61    spl3_13 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 9.34/1.61  fof(f134,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) ) | (~spl3_7 | ~spl3_13)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f94,f120])).
% 9.34/1.61  fof(f120,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl3_13),
% 9.34/1.61    inference(avatar_component_clause,[],[f119])).
% 9.34/1.61  fof(f303,plain,(
% 9.34/1.61    spl3_35 | ~spl3_3 | ~spl3_14),
% 9.34/1.61    inference(avatar_split_clause,[],[f143,f123,f77,f301])).
% 9.34/1.61  fof(f77,plain,(
% 9.34/1.61    spl3_3 <=> ! [X1] : r1_tarski(X1,X1)),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 9.34/1.61  fof(f123,plain,(
% 9.34/1.61    spl3_14 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 9.34/1.61    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 9.34/1.61  fof(f143,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) ) | (~spl3_3 | ~spl3_14)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f78,f124])).
% 9.34/1.61  fof(f124,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) ) | ~spl3_14),
% 9.34/1.61    inference(avatar_component_clause,[],[f123])).
% 9.34/1.61  fof(f78,plain,(
% 9.34/1.61    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl3_3),
% 9.34/1.61    inference(avatar_component_clause,[],[f77])).
% 9.34/1.61  fof(f294,plain,(
% 9.34/1.61    spl3_34 | ~spl3_3 | ~spl3_13),
% 9.34/1.61    inference(avatar_split_clause,[],[f133,f119,f77,f292])).
% 9.34/1.61  fof(f133,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) ) | (~spl3_3 | ~spl3_13)),
% 9.34/1.61    inference(unit_resulting_resolution,[],[f78,f120])).
% 9.34/1.61  fof(f168,plain,(
% 9.34/1.61    spl3_20),
% 9.34/1.61    inference(avatar_split_clause,[],[f54,f166])).
% 9.34/1.61  fof(f54,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 9.34/1.61    inference(cnf_transformation,[],[f34])).
% 9.34/1.61  fof(f34,plain,(
% 9.34/1.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 9.34/1.61    inference(flattening,[],[f33])).
% 9.34/1.61  fof(f33,plain,(
% 9.34/1.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 9.34/1.61    inference(nnf_transformation,[],[f23])).
% 9.34/1.61  fof(f23,axiom,(
% 9.34/1.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 9.34/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 9.34/1.61  fof(f129,plain,(
% 9.34/1.61    spl3_15),
% 9.34/1.61    inference(avatar_split_clause,[],[f49,f127])).
% 9.34/1.61  fof(f49,plain,(
% 9.34/1.61    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 9.34/1.61    inference(cnf_transformation,[],[f32])).
% 9.34/1.61  fof(f32,plain,(
% 9.34/1.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.34/1.61    inference(flattening,[],[f31])).
% 9.34/1.61  fof(f31,plain,(
% 9.34/1.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.34/1.61    inference(nnf_transformation,[],[f4])).
% 9.34/1.61  fof(f4,axiom,(
% 9.34/1.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 9.34/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 9.34/1.61  fof(f125,plain,(
% 9.34/1.61    spl3_14),
% 9.34/1.61    inference(avatar_split_clause,[],[f53,f123])).
% 9.34/1.61  fof(f53,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 9.34/1.61    inference(cnf_transformation,[],[f34])).
% 9.34/1.61  fof(f121,plain,(
% 9.34/1.61    spl3_13),
% 9.34/1.61    inference(avatar_split_clause,[],[f52,f119])).
% 9.34/1.61  fof(f52,plain,(
% 9.34/1.61    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 9.34/1.61    inference(cnf_transformation,[],[f34])).
% 9.34/1.61  fof(f113,plain,(
% 9.34/1.61    spl3_11),
% 9.34/1.61    inference(avatar_split_clause,[],[f44,f111])).
% 9.34/1.61  fof(f44,plain,(
% 9.34/1.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 9.34/1.61    inference(cnf_transformation,[],[f22])).
% 9.34/1.61  fof(f22,axiom,(
% 9.34/1.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 9.34/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 9.34/1.61  fof(f95,plain,(
% 9.34/1.61    spl3_7),
% 9.34/1.61    inference(avatar_split_clause,[],[f41,f93])).
% 9.34/1.61  fof(f41,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.34/1.61    inference(cnf_transformation,[],[f6])).
% 9.34/1.61  fof(f6,axiom,(
% 9.34/1.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.34/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 9.34/1.61  fof(f79,plain,(
% 9.34/1.61    spl3_3),
% 9.34/1.61    inference(avatar_split_clause,[],[f64,f77])).
% 9.34/1.61  fof(f64,plain,(
% 9.34/1.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 9.34/1.61    inference(equality_resolution,[],[f48])).
% 9.34/1.61  fof(f48,plain,(
% 9.34/1.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 9.34/1.61    inference(cnf_transformation,[],[f32])).
% 9.34/1.61  fof(f75,plain,(
% 9.34/1.61    spl3_2),
% 9.34/1.61    inference(avatar_split_clause,[],[f35,f72])).
% 9.34/1.61  fof(f35,plain,(
% 9.34/1.61    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 9.34/1.61    inference(cnf_transformation,[],[f30])).
% 9.34/1.61  fof(f30,plain,(
% 9.34/1.61    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 9.34/1.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 9.34/1.61  fof(f29,plain,(
% 9.34/1.61    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 9.34/1.61    introduced(choice_axiom,[])).
% 9.34/1.61  fof(f28,plain,(
% 9.34/1.61    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 9.34/1.61    inference(ennf_transformation,[],[f25])).
% 9.34/1.61  fof(f25,negated_conjecture,(
% 9.34/1.61    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 9.34/1.61    inference(negated_conjecture,[],[f24])).
% 9.34/1.61  fof(f24,conjecture,(
% 9.34/1.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 9.34/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 9.34/1.61  fof(f70,plain,(
% 9.34/1.61    ~spl3_1),
% 9.34/1.61    inference(avatar_split_clause,[],[f36,f67])).
% 9.34/1.61  fof(f36,plain,(
% 9.34/1.61    ~r2_hidden(sK0,sK2)),
% 9.34/1.61    inference(cnf_transformation,[],[f30])).
% 9.34/1.61  % SZS output end Proof for theBenchmark
% 9.34/1.61  % (12127)------------------------------
% 9.34/1.61  % (12127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.34/1.61  % (12127)Termination reason: Refutation
% 9.34/1.61  
% 9.34/1.61  % (12127)Memory used [KB]: 37227
% 9.34/1.61  % (12127)Time elapsed: 1.047 s
% 9.34/1.61  % (12127)------------------------------
% 9.34/1.61  % (12127)------------------------------
% 9.34/1.61  % (12096)Success in time 1.257 s
%------------------------------------------------------------------------------
