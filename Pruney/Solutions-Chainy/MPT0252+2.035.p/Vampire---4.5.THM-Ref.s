%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:55 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
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
fof(f5498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f81,f97,f119,f123,f127,f135,f177,f310,f319,f340,f1542,f2829,f4543,f4560,f4826,f5348,f5493])).

fof(f5493,plain,
    ( ~ spl3_7
    | spl3_34
    | ~ spl3_125 ),
    inference(avatar_contradiction_clause,[],[f5492])).

fof(f5492,plain,
    ( $false
    | ~ spl3_7
    | spl3_34
    | ~ spl3_125 ),
    inference(subsumption_resolution,[],[f299,f5416])).

fof(f5416,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl3_7
    | ~ spl3_125 ),
    inference(superposition,[],[f96,f5347])).

fof(f5347,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f5346])).

fof(f5346,plain,
    ( spl3_125
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f96,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f299,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl3_34
  <=> r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f5348,plain,
    ( spl3_125
    | ~ spl3_12
    | ~ spl3_113 ),
    inference(avatar_split_clause,[],[f5083,f4824,f117,f5346])).

fof(f117,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f4824,plain,
    ( spl3_113
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f5083,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl3_12
    | ~ spl3_113 ),
    inference(superposition,[],[f4825,f118])).

fof(f118,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f4825,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ spl3_113 ),
    inference(avatar_component_clause,[],[f4824])).

fof(f4826,plain,
    ( spl3_113
    | ~ spl3_12
    | ~ spl3_102 ),
    inference(avatar_split_clause,[],[f3767,f2827,f117,f4824])).

fof(f2827,plain,
    ( spl3_102
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f3767,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ spl3_12
    | ~ spl3_102 ),
    inference(superposition,[],[f118,f2828])).

fof(f2828,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_102 ),
    inference(avatar_component_clause,[],[f2827])).

fof(f4560,plain,
    ( ~ spl3_34
    | ~ spl3_2
    | ~ spl3_16
    | spl3_35 ),
    inference(avatar_split_clause,[],[f305,f301,f133,f74,f297])).

fof(f74,plain,
    ( spl3_2
  <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f301,plain,
    ( spl3_35
  <=> sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f305,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl3_2
    | ~ spl3_16
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f76,f302,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f302,plain,
    ( sK2 != k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_35 ),
    inference(avatar_component_clause,[],[f301])).

fof(f76,plain,
    ( r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f4543,plain,
    ( spl3_1
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(avatar_contradiction_clause,[],[f4542])).

fof(f4542,plain,
    ( $false
    | spl3_1
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f71,f4530])).

fof(f4530,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(superposition,[],[f339,f303])).

fof(f303,plain,
    ( sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f301])).

fof(f339,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl3_40
  <=> ! [X1,X0,X2] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2829,plain,
    ( spl3_102
    | ~ spl3_16
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f1551,f1540,f133,f2827])).

fof(f1540,plain,
    ( spl3_85
  <=> ! [X1,X0] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f1551,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_16
    | ~ spl3_85 ),
    inference(unit_resulting_resolution,[],[f1541,f1541,f134])).

fof(f1541,plain,
    ( ! [X0,X1] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1542,plain,
    ( spl3_85
    | ~ spl3_21
    | ~ spl3_36
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f320,f317,f308,f175,f1540])).

fof(f175,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f308,plain,
    ( spl3_36
  <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f317,plain,
    ( spl3_37
  <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f320,plain,
    ( ! [X0,X1] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))
    | ~ spl3_21
    | ~ spl3_36
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f309,f318,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f318,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f317])).

fof(f309,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f308])).

fof(f340,plain,
    ( spl3_40
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f144,f121,f95,f338])).

fof(f121,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f144,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f96,f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f319,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f149,f125,f79,f317])).

fof(f79,plain,
    ( spl3_3
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f125,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f149,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0))
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f80,f126])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f80,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f310,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f143,f121,f79,f308])).

fof(f143,plain,
    ( ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f80,f122])).

fof(f177,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f56,f175])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f135,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f51,f133])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f127,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f46,f117])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f97,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f81,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f66,f79])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f72,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (32435)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.49  % (32427)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (32428)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (32428)Refutation not found, incomplete strategy% (32428)------------------------------
% 0.21/0.52  % (32428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32428)Memory used [KB]: 1663
% 0.21/0.52  % (32428)Time elapsed: 0.008 s
% 0.21/0.52  % (32428)------------------------------
% 0.21/0.52  % (32428)------------------------------
% 0.21/0.52  % (32420)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32417)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (32421)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (32436)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (32430)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (32430)Refutation not found, incomplete strategy% (32430)------------------------------
% 0.21/0.53  % (32430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32430)Memory used [KB]: 10618
% 0.21/0.53  % (32430)Time elapsed: 0.110 s
% 0.21/0.53  % (32430)------------------------------
% 0.21/0.53  % (32430)------------------------------
% 0.21/0.54  % (32422)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (32416)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (32419)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (32418)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (32424)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (32415)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (32415)Refutation not found, incomplete strategy% (32415)------------------------------
% 0.21/0.55  % (32415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32415)Memory used [KB]: 1663
% 0.21/0.55  % (32415)Time elapsed: 0.144 s
% 0.21/0.55  % (32415)------------------------------
% 0.21/0.55  % (32415)------------------------------
% 0.21/0.55  % (32414)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (32441)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (32441)Refutation not found, incomplete strategy% (32441)------------------------------
% 0.21/0.55  % (32441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32441)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32441)Memory used [KB]: 6140
% 0.21/0.55  % (32441)Time elapsed: 0.147 s
% 0.21/0.55  % (32441)------------------------------
% 0.21/0.55  % (32441)------------------------------
% 0.21/0.55  % (32440)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32443)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (32443)Refutation not found, incomplete strategy% (32443)------------------------------
% 0.21/0.55  % (32443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32443)Memory used [KB]: 1663
% 0.21/0.55  % (32443)Time elapsed: 0.159 s
% 0.21/0.55  % (32443)------------------------------
% 0.21/0.55  % (32443)------------------------------
% 0.21/0.55  % (32440)Refutation not found, incomplete strategy% (32440)------------------------------
% 0.21/0.55  % (32440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32440)Memory used [KB]: 6140
% 0.21/0.55  % (32440)Time elapsed: 0.153 s
% 0.21/0.55  % (32440)------------------------------
% 0.21/0.55  % (32440)------------------------------
% 0.21/0.55  % (32432)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (32432)Refutation not found, incomplete strategy% (32432)------------------------------
% 0.21/0.56  % (32432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32432)Memory used [KB]: 1663
% 0.21/0.56  % (32432)Time elapsed: 0.155 s
% 0.21/0.56  % (32432)------------------------------
% 0.21/0.56  % (32432)------------------------------
% 0.21/0.56  % (32431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (32433)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (32424)Refutation not found, incomplete strategy% (32424)------------------------------
% 0.21/0.56  % (32424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32424)Memory used [KB]: 10874
% 0.21/0.56  % (32424)Time elapsed: 0.157 s
% 0.21/0.56  % (32424)------------------------------
% 0.21/0.56  % (32424)------------------------------
% 0.21/0.56  % (32425)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (32425)Refutation not found, incomplete strategy% (32425)------------------------------
% 0.21/0.56  % (32425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32425)Memory used [KB]: 6396
% 0.21/0.56  % (32425)Time elapsed: 0.159 s
% 0.21/0.56  % (32425)------------------------------
% 0.21/0.56  % (32425)------------------------------
% 0.21/0.56  % (32437)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (32442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (32438)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (32439)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (32439)Refutation not found, incomplete strategy% (32439)------------------------------
% 0.21/0.57  % (32439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32439)Memory used [KB]: 6140
% 0.21/0.57  % (32439)Time elapsed: 0.166 s
% 0.21/0.57  % (32439)------------------------------
% 0.21/0.57  % (32439)------------------------------
% 0.21/0.57  % (32438)Refutation not found, incomplete strategy% (32438)------------------------------
% 0.21/0.57  % (32438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32438)Memory used [KB]: 10746
% 0.21/0.57  % (32438)Time elapsed: 0.161 s
% 0.21/0.57  % (32438)------------------------------
% 0.21/0.57  % (32438)------------------------------
% 0.21/0.57  % (32442)Refutation not found, incomplete strategy% (32442)------------------------------
% 0.21/0.57  % (32442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32442)Memory used [KB]: 10874
% 0.21/0.57  % (32442)Time elapsed: 0.167 s
% 0.21/0.57  % (32442)------------------------------
% 0.21/0.57  % (32442)------------------------------
% 0.21/0.57  % (32423)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (32429)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (32434)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.58  % (32431)Refutation not found, incomplete strategy% (32431)------------------------------
% 0.21/0.58  % (32431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (32431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (32431)Memory used [KB]: 1791
% 0.21/0.58  % (32431)Time elapsed: 0.176 s
% 0.21/0.58  % (32431)------------------------------
% 0.21/0.58  % (32431)------------------------------
% 0.21/0.58  % (32426)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.58  % (32426)Refutation not found, incomplete strategy% (32426)------------------------------
% 0.21/0.58  % (32426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (32426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (32426)Memory used [KB]: 10618
% 0.21/0.58  % (32426)Time elapsed: 0.179 s
% 0.21/0.58  % (32426)------------------------------
% 0.21/0.58  % (32426)------------------------------
% 2.08/0.63  % (32470)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.30/0.68  % (32422)Refutation not found, incomplete strategy% (32422)------------------------------
% 2.30/0.68  % (32422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.68  % (32422)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.68  
% 2.30/0.68  % (32422)Memory used [KB]: 6140
% 2.30/0.68  % (32422)Time elapsed: 0.231 s
% 2.30/0.68  % (32422)------------------------------
% 2.30/0.68  % (32422)------------------------------
% 2.30/0.68  % (32473)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.30/0.68  % (32476)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.30/0.69  % (32477)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.30/0.69  % (32477)Refutation not found, incomplete strategy% (32477)------------------------------
% 2.30/0.69  % (32477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (32477)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.69  
% 2.30/0.69  % (32477)Memory used [KB]: 10746
% 2.30/0.69  % (32477)Time elapsed: 0.103 s
% 2.30/0.69  % (32477)------------------------------
% 2.30/0.69  % (32477)------------------------------
% 2.30/0.69  % (32476)Refutation not found, incomplete strategy% (32476)------------------------------
% 2.30/0.69  % (32476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (32476)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.69  
% 2.30/0.69  % (32476)Memory used [KB]: 10618
% 2.30/0.69  % (32476)Time elapsed: 0.073 s
% 2.30/0.69  % (32476)------------------------------
% 2.30/0.69  % (32476)------------------------------
% 2.30/0.69  % (32417)Refutation not found, incomplete strategy% (32417)------------------------------
% 2.30/0.69  % (32417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (32417)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.69  
% 2.30/0.69  % (32417)Memory used [KB]: 6140
% 2.30/0.69  % (32417)Time elapsed: 0.263 s
% 2.30/0.69  % (32417)------------------------------
% 2.30/0.69  % (32417)------------------------------
% 2.30/0.70  % (32478)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.30/0.71  % (32478)Refutation not found, incomplete strategy% (32478)------------------------------
% 2.30/0.71  % (32478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.71  % (32479)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.30/0.71  % (32478)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.71  
% 2.30/0.71  % (32478)Memory used [KB]: 1791
% 2.30/0.71  % (32478)Time elapsed: 0.122 s
% 2.30/0.71  % (32478)------------------------------
% 2.30/0.71  % (32478)------------------------------
% 2.30/0.71  % (32479)Refutation not found, incomplete strategy% (32479)------------------------------
% 2.30/0.71  % (32479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.71  % (32479)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.71  
% 2.30/0.71  % (32479)Memory used [KB]: 10618
% 2.30/0.71  % (32479)Time elapsed: 0.113 s
% 2.30/0.71  % (32479)------------------------------
% 2.30/0.71  % (32479)------------------------------
% 2.81/0.71  % (32416)Refutation not found, incomplete strategy% (32416)------------------------------
% 2.81/0.71  % (32416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.71  % (32416)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.71  
% 2.81/0.71  % (32416)Memory used [KB]: 6268
% 2.81/0.71  % (32416)Time elapsed: 0.305 s
% 2.81/0.71  % (32416)------------------------------
% 2.81/0.71  % (32416)------------------------------
% 2.81/0.72  % (32482)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.81/0.72  % (32482)Refutation not found, incomplete strategy% (32482)------------------------------
% 2.81/0.72  % (32482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.72  % (32482)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.72  
% 2.81/0.72  % (32482)Memory used [KB]: 10746
% 2.81/0.72  % (32482)Time elapsed: 0.133 s
% 2.81/0.72  % (32482)------------------------------
% 2.81/0.72  % (32482)------------------------------
% 2.81/0.73  % (32475)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.81/0.73  % (32480)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.81/0.73  % (32475)Refutation not found, incomplete strategy% (32475)------------------------------
% 2.81/0.73  % (32475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.73  % (32475)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.73  
% 2.81/0.73  % (32475)Memory used [KB]: 6268
% 2.81/0.73  % (32475)Time elapsed: 0.126 s
% 2.81/0.73  % (32475)------------------------------
% 2.81/0.73  % (32475)------------------------------
% 2.81/0.73  % (32481)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.81/0.74  % (32484)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.81/0.74  % (32483)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.81/0.74  % (32484)Refutation not found, incomplete strategy% (32484)------------------------------
% 2.81/0.74  % (32484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.74  % (32484)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.74  
% 2.81/0.74  % (32484)Memory used [KB]: 10746
% 2.81/0.74  % (32484)Time elapsed: 0.143 s
% 2.81/0.74  % (32484)------------------------------
% 2.81/0.74  % (32484)------------------------------
% 2.81/0.75  % (32486)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.81/0.75  % (32414)Refutation not found, incomplete strategy% (32414)------------------------------
% 2.81/0.75  % (32414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.76  % (32486)Refutation not found, incomplete strategy% (32486)------------------------------
% 2.81/0.76  % (32486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.76  % (32486)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.76  
% 2.81/0.76  % (32486)Memory used [KB]: 10746
% 2.81/0.76  % (32486)Time elapsed: 0.155 s
% 2.81/0.76  % (32486)------------------------------
% 2.81/0.76  % (32486)------------------------------
% 3.10/0.76  % (32429)Refutation not found, incomplete strategy% (32429)------------------------------
% 3.10/0.76  % (32429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.76  % (32429)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.76  
% 3.10/0.76  % (32429)Memory used [KB]: 6140
% 3.10/0.76  % (32429)Time elapsed: 0.360 s
% 3.10/0.76  % (32429)------------------------------
% 3.10/0.76  % (32429)------------------------------
% 3.10/0.77  % (32485)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.10/0.77  % (32489)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.10/0.77  % (32414)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.77  
% 3.10/0.77  % (32414)Memory used [KB]: 1791
% 3.10/0.77  % (32414)Time elapsed: 0.350 s
% 3.10/0.77  % (32414)------------------------------
% 3.10/0.77  % (32414)------------------------------
% 3.10/0.79  % (32490)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.10/0.79  % (32491)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.10/0.80  % (32492)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.10/0.81  % (32494)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.10/0.81  % (32493)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.10/0.81  % (32485)Refutation not found, incomplete strategy% (32485)------------------------------
% 3.10/0.81  % (32485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.81  % (32485)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.81  
% 3.10/0.81  % (32485)Memory used [KB]: 2302
% 3.10/0.81  % (32485)Time elapsed: 0.201 s
% 3.10/0.81  % (32485)------------------------------
% 3.10/0.81  % (32485)------------------------------
% 3.10/0.82  % (32494)Refutation not found, incomplete strategy% (32494)------------------------------
% 3.10/0.82  % (32494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.82  % (32494)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.82  
% 3.10/0.82  % (32494)Memory used [KB]: 1663
% 3.10/0.82  % (32494)Time elapsed: 0.074 s
% 3.10/0.82  % (32494)------------------------------
% 3.10/0.82  % (32494)------------------------------
% 3.63/0.85  % (32495)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.63/0.87  % (32481)Refutation not found, incomplete strategy% (32481)------------------------------
% 3.63/0.87  % (32481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.87  % (32481)Termination reason: Refutation not found, incomplete strategy
% 3.63/0.87  
% 3.63/0.87  % (32481)Memory used [KB]: 6140
% 3.63/0.87  % (32481)Time elapsed: 0.264 s
% 3.63/0.87  % (32481)------------------------------
% 3.63/0.87  % (32481)------------------------------
% 3.86/0.89  % (32489)Refutation not found, incomplete strategy% (32489)------------------------------
% 3.86/0.89  % (32489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.89  % (32489)Termination reason: Refutation not found, incomplete strategy
% 3.86/0.89  
% 3.86/0.89  % (32489)Memory used [KB]: 6268
% 3.86/0.89  % (32489)Time elapsed: 0.170 s
% 3.86/0.89  % (32489)------------------------------
% 3.86/0.89  % (32489)------------------------------
% 3.86/0.90  % (32490)Refutation not found, incomplete strategy% (32490)------------------------------
% 3.86/0.90  % (32490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.91  % (32490)Termination reason: Refutation not found, incomplete strategy
% 3.86/0.91  
% 3.86/0.91  % (32490)Memory used [KB]: 6140
% 3.86/0.91  % (32490)Time elapsed: 0.181 s
% 3.86/0.91  % (32490)------------------------------
% 3.86/0.91  % (32490)------------------------------
% 4.38/1.00  % (32420)Time limit reached!
% 4.38/1.00  % (32420)------------------------------
% 4.38/1.00  % (32420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/1.00  % (32420)Termination reason: Time limit
% 4.38/1.00  % (32420)Termination phase: Saturation
% 4.38/1.00  
% 4.38/1.00  % (32420)Memory used [KB]: 16758
% 4.38/1.00  % (32420)Time elapsed: 0.500 s
% 4.38/1.00  % (32420)------------------------------
% 4.38/1.00  % (32420)------------------------------
% 4.74/1.03  % (32421)Time limit reached!
% 4.74/1.03  % (32421)------------------------------
% 4.74/1.03  % (32421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (32421)Termination reason: Time limit
% 4.74/1.03  % (32421)Termination phase: Saturation
% 4.74/1.03  
% 4.74/1.03  % (32421)Memory used [KB]: 7675
% 4.74/1.03  % (32421)Time elapsed: 0.600 s
% 4.74/1.03  % (32421)------------------------------
% 4.74/1.03  % (32421)------------------------------
% 5.02/1.14  % (32492)Time limit reached!
% 5.02/1.14  % (32492)------------------------------
% 5.02/1.14  % (32492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.14  % (32492)Termination reason: Time limit
% 5.02/1.14  
% 5.02/1.14  % (32492)Memory used [KB]: 14967
% 5.02/1.14  % (32492)Time elapsed: 0.408 s
% 5.02/1.14  % (32492)------------------------------
% 5.02/1.14  % (32492)------------------------------
% 5.02/1.14  % (32470)Refutation found. Thanks to Tanya!
% 5.02/1.14  % SZS status Theorem for theBenchmark
% 5.02/1.14  % SZS output start Proof for theBenchmark
% 5.02/1.14  fof(f5498,plain,(
% 5.02/1.14    $false),
% 5.02/1.14    inference(avatar_sat_refutation,[],[f72,f77,f81,f97,f119,f123,f127,f135,f177,f310,f319,f340,f1542,f2829,f4543,f4560,f4826,f5348,f5493])).
% 5.02/1.14  fof(f5493,plain,(
% 5.02/1.14    ~spl3_7 | spl3_34 | ~spl3_125),
% 5.02/1.14    inference(avatar_contradiction_clause,[],[f5492])).
% 5.02/1.14  fof(f5492,plain,(
% 5.02/1.14    $false | (~spl3_7 | spl3_34 | ~spl3_125)),
% 5.02/1.14    inference(subsumption_resolution,[],[f299,f5416])).
% 5.02/1.14  fof(f5416,plain,(
% 5.02/1.14    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | (~spl3_7 | ~spl3_125)),
% 5.02/1.14    inference(superposition,[],[f96,f5347])).
% 5.02/1.14  fof(f5347,plain,(
% 5.02/1.14    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl3_125),
% 5.02/1.14    inference(avatar_component_clause,[],[f5346])).
% 5.02/1.14  fof(f5346,plain,(
% 5.02/1.14    spl3_125 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 5.02/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 5.02/1.14  fof(f96,plain,(
% 5.02/1.14    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_7),
% 5.02/1.14    inference(avatar_component_clause,[],[f95])).
% 5.02/1.14  fof(f95,plain,(
% 5.02/1.14    spl3_7 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.02/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 5.02/1.14  fof(f299,plain,(
% 5.02/1.14    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_34),
% 5.02/1.14    inference(avatar_component_clause,[],[f297])).
% 5.02/1.14  fof(f297,plain,(
% 5.02/1.14    spl3_34 <=> r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 5.02/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 5.02/1.15  fof(f5348,plain,(
% 5.02/1.15    spl3_125 | ~spl3_12 | ~spl3_113),
% 5.02/1.15    inference(avatar_split_clause,[],[f5083,f4824,f117,f5346])).
% 5.02/1.15  fof(f117,plain,(
% 5.02/1.15    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 5.02/1.15  fof(f4824,plain,(
% 5.02/1.15    spl3_113 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 5.02/1.15  fof(f5083,plain,(
% 5.02/1.15    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl3_12 | ~spl3_113)),
% 5.02/1.15    inference(superposition,[],[f4825,f118])).
% 5.02/1.15  fof(f118,plain,(
% 5.02/1.15    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl3_12),
% 5.02/1.15    inference(avatar_component_clause,[],[f117])).
% 5.02/1.15  fof(f4825,plain,(
% 5.02/1.15    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))) ) | ~spl3_113),
% 5.02/1.15    inference(avatar_component_clause,[],[f4824])).
% 5.02/1.15  fof(f4826,plain,(
% 5.02/1.15    spl3_113 | ~spl3_12 | ~spl3_102),
% 5.02/1.15    inference(avatar_split_clause,[],[f3767,f2827,f117,f4824])).
% 5.02/1.15  fof(f2827,plain,(
% 5.02/1.15    spl3_102 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 5.02/1.15  fof(f3767,plain,(
% 5.02/1.15    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k3_tarski(k2_tarski(X3,X2))) ) | (~spl3_12 | ~spl3_102)),
% 5.02/1.15    inference(superposition,[],[f118,f2828])).
% 5.02/1.15  fof(f2828,plain,(
% 5.02/1.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_102),
% 5.02/1.15    inference(avatar_component_clause,[],[f2827])).
% 5.02/1.15  fof(f4560,plain,(
% 5.02/1.15    ~spl3_34 | ~spl3_2 | ~spl3_16 | spl3_35),
% 5.02/1.15    inference(avatar_split_clause,[],[f305,f301,f133,f74,f297])).
% 5.02/1.15  fof(f74,plain,(
% 5.02/1.15    spl3_2 <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.02/1.15  fof(f133,plain,(
% 5.02/1.15    spl3_16 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 5.02/1.15  fof(f301,plain,(
% 5.02/1.15    spl3_35 <=> sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 5.02/1.15  fof(f305,plain,(
% 5.02/1.15    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | (~spl3_2 | ~spl3_16 | spl3_35)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f76,f302,f134])).
% 5.02/1.15  fof(f134,plain,(
% 5.02/1.15    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 5.02/1.15    inference(avatar_component_clause,[],[f133])).
% 5.02/1.15  fof(f302,plain,(
% 5.02/1.15    sK2 != k2_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_35),
% 5.02/1.15    inference(avatar_component_clause,[],[f301])).
% 5.02/1.15  fof(f76,plain,(
% 5.02/1.15    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | ~spl3_2),
% 5.02/1.15    inference(avatar_component_clause,[],[f74])).
% 5.02/1.15  fof(f4543,plain,(
% 5.02/1.15    spl3_1 | ~spl3_35 | ~spl3_40),
% 5.02/1.15    inference(avatar_contradiction_clause,[],[f4542])).
% 5.02/1.15  fof(f4542,plain,(
% 5.02/1.15    $false | (spl3_1 | ~spl3_35 | ~spl3_40)),
% 5.02/1.15    inference(subsumption_resolution,[],[f71,f4530])).
% 5.02/1.15  fof(f4530,plain,(
% 5.02/1.15    r2_hidden(sK0,sK2) | (~spl3_35 | ~spl3_40)),
% 5.02/1.15    inference(superposition,[],[f339,f303])).
% 5.02/1.15  fof(f303,plain,(
% 5.02/1.15    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_35),
% 5.02/1.15    inference(avatar_component_clause,[],[f301])).
% 5.02/1.15  fof(f339,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl3_40),
% 5.02/1.15    inference(avatar_component_clause,[],[f338])).
% 5.02/1.15  fof(f338,plain,(
% 5.02/1.15    spl3_40 <=> ! [X1,X0,X2] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 5.02/1.15  fof(f71,plain,(
% 5.02/1.15    ~r2_hidden(sK0,sK2) | spl3_1),
% 5.02/1.15    inference(avatar_component_clause,[],[f69])).
% 5.02/1.15  fof(f69,plain,(
% 5.02/1.15    spl3_1 <=> r2_hidden(sK0,sK2)),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.02/1.15  fof(f2829,plain,(
% 5.02/1.15    spl3_102 | ~spl3_16 | ~spl3_85),
% 5.02/1.15    inference(avatar_split_clause,[],[f1551,f1540,f133,f2827])).
% 5.02/1.15  fof(f1540,plain,(
% 5.02/1.15    spl3_85 <=> ! [X1,X0] : r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 5.02/1.15  fof(f1551,plain,(
% 5.02/1.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | (~spl3_16 | ~spl3_85)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f1541,f1541,f134])).
% 5.02/1.15  fof(f1541,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))) ) | ~spl3_85),
% 5.02/1.15    inference(avatar_component_clause,[],[f1540])).
% 5.02/1.15  fof(f1542,plain,(
% 5.02/1.15    spl3_85 | ~spl3_21 | ~spl3_36 | ~spl3_37),
% 5.02/1.15    inference(avatar_split_clause,[],[f320,f317,f308,f175,f1540])).
% 5.02/1.15  fof(f175,plain,(
% 5.02/1.15    spl3_21 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 5.02/1.15  fof(f308,plain,(
% 5.02/1.15    spl3_36 <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X0,X1))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 5.02/1.15  fof(f317,plain,(
% 5.02/1.15    spl3_37 <=> ! [X1,X0] : r2_hidden(X0,k2_tarski(X1,X0))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 5.02/1.15  fof(f320,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k2_tarski(X1,X0))) ) | (~spl3_21 | ~spl3_36 | ~spl3_37)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f309,f318,f176])).
% 5.02/1.15  fof(f176,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) ) | ~spl3_21),
% 5.02/1.15    inference(avatar_component_clause,[],[f175])).
% 5.02/1.15  fof(f318,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) ) | ~spl3_37),
% 5.02/1.15    inference(avatar_component_clause,[],[f317])).
% 5.02/1.15  fof(f309,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) ) | ~spl3_36),
% 5.02/1.15    inference(avatar_component_clause,[],[f308])).
% 5.02/1.15  fof(f340,plain,(
% 5.02/1.15    spl3_40 | ~spl3_7 | ~spl3_13),
% 5.02/1.15    inference(avatar_split_clause,[],[f144,f121,f95,f338])).
% 5.02/1.15  fof(f121,plain,(
% 5.02/1.15    spl3_13 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 5.02/1.15  fof(f144,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) ) | (~spl3_7 | ~spl3_13)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f96,f122])).
% 5.02/1.15  fof(f122,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl3_13),
% 5.02/1.15    inference(avatar_component_clause,[],[f121])).
% 5.02/1.15  fof(f319,plain,(
% 5.02/1.15    spl3_37 | ~spl3_3 | ~spl3_14),
% 5.02/1.15    inference(avatar_split_clause,[],[f149,f125,f79,f317])).
% 5.02/1.15  fof(f79,plain,(
% 5.02/1.15    spl3_3 <=> ! [X1] : r1_tarski(X1,X1)),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.02/1.15  fof(f125,plain,(
% 5.02/1.15    spl3_14 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 5.02/1.15    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 5.02/1.15  fof(f149,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) ) | (~spl3_3 | ~spl3_14)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f80,f126])).
% 5.02/1.15  fof(f126,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) ) | ~spl3_14),
% 5.02/1.15    inference(avatar_component_clause,[],[f125])).
% 5.02/1.15  fof(f80,plain,(
% 5.02/1.15    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl3_3),
% 5.02/1.15    inference(avatar_component_clause,[],[f79])).
% 5.02/1.15  fof(f310,plain,(
% 5.02/1.15    spl3_36 | ~spl3_3 | ~spl3_13),
% 5.02/1.15    inference(avatar_split_clause,[],[f143,f121,f79,f308])).
% 5.02/1.15  fof(f143,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) ) | (~spl3_3 | ~spl3_13)),
% 5.02/1.15    inference(unit_resulting_resolution,[],[f80,f122])).
% 5.02/1.15  fof(f177,plain,(
% 5.02/1.15    spl3_21),
% 5.02/1.15    inference(avatar_split_clause,[],[f56,f175])).
% 5.02/1.15  fof(f56,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 5.02/1.15    inference(cnf_transformation,[],[f35])).
% 5.02/1.15  fof(f35,plain,(
% 5.02/1.15    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 5.02/1.15    inference(flattening,[],[f34])).
% 5.02/1.15  fof(f34,plain,(
% 5.02/1.15    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 5.02/1.15    inference(nnf_transformation,[],[f24])).
% 5.02/1.15  fof(f24,axiom,(
% 5.02/1.15    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 5.02/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 5.02/1.15  fof(f135,plain,(
% 5.02/1.15    spl3_16),
% 5.02/1.15    inference(avatar_split_clause,[],[f51,f133])).
% 5.02/1.15  fof(f51,plain,(
% 5.02/1.15    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 5.02/1.15    inference(cnf_transformation,[],[f33])).
% 5.02/1.15  fof(f33,plain,(
% 5.02/1.15    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.02/1.15    inference(flattening,[],[f32])).
% 5.02/1.15  fof(f32,plain,(
% 5.02/1.15    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.02/1.15    inference(nnf_transformation,[],[f4])).
% 5.02/1.15  fof(f4,axiom,(
% 5.02/1.15    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.02/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.02/1.15  fof(f127,plain,(
% 5.02/1.15    spl3_14),
% 5.02/1.15    inference(avatar_split_clause,[],[f55,f125])).
% 5.02/1.15  fof(f55,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 5.02/1.15    inference(cnf_transformation,[],[f35])).
% 5.02/1.15  fof(f123,plain,(
% 5.02/1.15    spl3_13),
% 5.02/1.15    inference(avatar_split_clause,[],[f54,f121])).
% 5.02/1.15  fof(f54,plain,(
% 5.02/1.15    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 5.02/1.15    inference(cnf_transformation,[],[f35])).
% 5.02/1.15  fof(f119,plain,(
% 5.02/1.15    spl3_12),
% 5.02/1.15    inference(avatar_split_clause,[],[f46,f117])).
% 5.02/1.15  fof(f46,plain,(
% 5.02/1.15    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.02/1.15    inference(cnf_transformation,[],[f23])).
% 5.02/1.15  fof(f23,axiom,(
% 5.02/1.15    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.02/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.02/1.15  fof(f97,plain,(
% 5.02/1.15    spl3_7),
% 5.02/1.15    inference(avatar_split_clause,[],[f42,f95])).
% 5.02/1.15  fof(f42,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.02/1.15    inference(cnf_transformation,[],[f6])).
% 5.02/1.15  fof(f6,axiom,(
% 5.02/1.15    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.02/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 5.02/1.15  fof(f81,plain,(
% 5.02/1.15    spl3_3),
% 5.02/1.15    inference(avatar_split_clause,[],[f66,f79])).
% 5.02/1.15  fof(f66,plain,(
% 5.02/1.15    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.02/1.15    inference(equality_resolution,[],[f50])).
% 5.02/1.15  fof(f50,plain,(
% 5.02/1.15    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.02/1.15    inference(cnf_transformation,[],[f33])).
% 5.02/1.15  fof(f77,plain,(
% 5.02/1.15    spl3_2),
% 5.02/1.15    inference(avatar_split_clause,[],[f36,f74])).
% 5.02/1.15  fof(f36,plain,(
% 5.02/1.15    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 5.02/1.15    inference(cnf_transformation,[],[f31])).
% 5.02/1.15  fof(f31,plain,(
% 5.02/1.15    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 5.02/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 5.02/1.15  fof(f30,plain,(
% 5.02/1.15    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 5.02/1.15    introduced(choice_axiom,[])).
% 5.02/1.15  fof(f29,plain,(
% 5.02/1.15    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 5.02/1.15    inference(ennf_transformation,[],[f26])).
% 5.02/1.15  fof(f26,negated_conjecture,(
% 5.02/1.15    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 5.02/1.15    inference(negated_conjecture,[],[f25])).
% 5.02/1.15  fof(f25,conjecture,(
% 5.02/1.15    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 5.02/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 5.02/1.15  fof(f72,plain,(
% 5.02/1.15    ~spl3_1),
% 5.02/1.15    inference(avatar_split_clause,[],[f37,f69])).
% 5.02/1.15  fof(f37,plain,(
% 5.02/1.15    ~r2_hidden(sK0,sK2)),
% 5.02/1.15    inference(cnf_transformation,[],[f31])).
% 5.02/1.15  % SZS output end Proof for theBenchmark
% 5.02/1.15  % (32470)------------------------------
% 5.02/1.15  % (32470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.15  % (32470)Termination reason: Refutation
% 5.02/1.15  
% 5.02/1.15  % (32470)Memory used [KB]: 17526
% 5.02/1.15  % (32470)Time elapsed: 0.552 s
% 5.02/1.15  % (32470)------------------------------
% 5.02/1.15  % (32470)------------------------------
% 5.02/1.15  % (32413)Success in time 0.798 s
%------------------------------------------------------------------------------
