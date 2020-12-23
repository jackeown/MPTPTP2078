%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 123 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 243 expanded)
%              Number of equality atoms :    8 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1090,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f65,f1026,f1028,f1089])).

fof(f1089,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f1088])).

fof(f1088,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f1070,f135])).

fof(f135,plain,
    ( ! [X0] : r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5))))
    | ~ spl6_2 ),
    inference(superposition,[],[f57,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f57,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5))))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f46,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1070,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f1025,f103])).

fof(f103,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(X11,k2_zfmisc_1(X10,X9))
      | r1_tarski(X11,k2_zfmisc_1(k3_tarski(k2_tarski(X8,X10)),X9)) ) ),
    inference(superposition,[],[f36,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1025,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1023,plain,
    ( spl6_7
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1028,plain,
    ( ~ spl6_1
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f1027])).

fof(f1027,plain,
    ( $false
    | ~ spl6_1
    | spl6_6 ),
    inference(subsumption_resolution,[],[f1021,f384])).

fof(f384,plain,
    ( ! [X0,X1] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK3,X1))))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f93,f69,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1)) ),
    inference(unit_resulting_resolution,[],[f33,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f93,plain,
    ( ! [X0] : r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0))))
    | ~ spl6_1 ),
    inference(superposition,[],[f48,f34])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f33,f30])).

fof(f41,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1021,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1019,plain,
    ( spl6_6
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1026,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_3 ),
    inference(avatar_split_clause,[],[f91,f62,f1023,f1019])).

fof(f62,plain,
    ( spl6_3
  <=> r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_3 ),
    inference(resolution,[],[f37,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f65,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f22,f24,f24,f24])).

fof(f22,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (6720)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (6720)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1090,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f42,f47,f65,f1026,f1028,f1089])).
% 0.21/0.48  fof(f1089,plain,(
% 0.21/0.48    ~spl6_2 | spl6_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1088])).
% 0.21/0.48  fof(f1088,plain,(
% 0.21/0.48    $false | (~spl6_2 | spl6_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1070,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5))))) ) | ~spl6_2),
% 0.21/0.48    inference(superposition,[],[f57,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f24,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5))))) ) | ~spl6_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f1070,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | spl6_7),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f1025,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X10,X8,X11,X9] : (~r1_tarski(X11,k2_zfmisc_1(X10,X9)) | r1_tarski(X11,k2_zfmisc_1(k3_tarski(k2_tarski(X8,X10)),X9))) )),
% 0.21/0.48    inference(superposition,[],[f36,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f24,f24])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f1025,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f1023])).
% 0.21/0.48  fof(f1023,plain,(
% 0.21/0.48    spl6_7 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f1028,plain,(
% 0.21/0.48    ~spl6_1 | spl6_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1027])).
% 0.21/0.48  fof(f1027,plain,(
% 0.21/0.48    $false | (~spl6_1 | spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1021,f384])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK3,X1))))) ) | ~spl6_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f93,f69,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f33,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f24])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0))))) ) | ~spl6_1),
% 0.21/0.48    inference(superposition,[],[f48,f34])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0)))) ) | ~spl6_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f41,f33,f30])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f1021,plain,(
% 0.21/0.48    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f1019])).
% 0.21/0.48  fof(f1019,plain,(
% 0.21/0.48    spl6_6 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f1026,plain,(
% 0.21/0.48    ~spl6_6 | ~spl6_7 | spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f62,f1023,f1019])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl6_3 <=> r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_3),
% 0.21/0.48    inference(resolution,[],[f37,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f31,f24])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f62])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f24,f24,f24])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6720)------------------------------
% 0.21/0.48  % (6720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6720)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6720)Memory used [KB]: 12409
% 0.21/0.48  % (6720)Time elapsed: 0.060 s
% 0.21/0.48  % (6720)------------------------------
% 0.21/0.48  % (6720)------------------------------
% 0.21/0.48  % (6704)Success in time 0.129 s
%------------------------------------------------------------------------------
