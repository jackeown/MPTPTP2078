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
% DateTime   : Thu Dec  3 12:32:42 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 185 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 ( 591 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f942,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f927,f941])).

fof(f941,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f938])).

fof(f938,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f25,f932])).

fof(f932,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(X0,sK2))
    | spl4_2 ),
    inference(resolution,[],[f928,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f928,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r1_tarski(sK0,X0) )
    | spl4_2 ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f25,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f927,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f920,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f920,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_1 ),
    inference(resolution,[],[f747,f470])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_1 ),
    inference(resolution,[],[f460,f452])).

fof(f452,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f73,f31])).

fof(f73,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK3(X4,X3),X5)
      | r1_tarski(X4,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X5,X2) ) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f30,f32])).

fof(f460,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl4_1 ),
    inference(resolution,[],[f453,f25])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_1 ),
    inference(resolution,[],[f452,f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f747,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(subsumption_resolution,[],[f725,f27])).

fof(f725,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | ~ r1_xboole_0(k4_xboole_0(X2,X3),X3) ) ),
    inference(resolution,[],[f77,f235])).

fof(f235,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X3) ),
    inference(subsumption_resolution,[],[f230,f52])).

fof(f52,plain,(
    ! [X4,X5,X3] : r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X2)
      | r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X3) ) ),
    inference(resolution,[],[f179,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f179,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k2_xboole_0(X7,X6)) ),
    inference(resolution,[],[f98,f52])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X3) ) ),
    inference(resolution,[],[f94,f36])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f89,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f49,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0))
      | r1_tarski(X2,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)
      | r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X3) ) ),
    inference(superposition,[],[f63,f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      | r1_tarski(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f36,f34])).

fof(f45,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f42,f38])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:56:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (781156352)
% 0.15/0.38  ipcrm: permission denied for id (781221890)
% 0.15/0.38  ipcrm: permission denied for id (781287428)
% 0.15/0.38  ipcrm: permission denied for id (781352966)
% 0.15/0.38  ipcrm: permission denied for id (781418504)
% 0.15/0.39  ipcrm: permission denied for id (781516811)
% 0.15/0.39  ipcrm: permission denied for id (781582349)
% 0.15/0.39  ipcrm: permission denied for id (781615118)
% 0.15/0.39  ipcrm: permission denied for id (781647887)
% 0.15/0.40  ipcrm: permission denied for id (785481745)
% 0.15/0.40  ipcrm: permission denied for id (781778963)
% 0.15/0.40  ipcrm: permission denied for id (781844501)
% 0.15/0.40  ipcrm: permission denied for id (781877270)
% 0.15/0.40  ipcrm: permission denied for id (785580055)
% 0.15/0.40  ipcrm: permission denied for id (781942808)
% 0.15/0.41  ipcrm: permission denied for id (781975577)
% 0.15/0.41  ipcrm: permission denied for id (782008346)
% 0.15/0.41  ipcrm: permission denied for id (785612827)
% 0.15/0.41  ipcrm: permission denied for id (782073884)
% 0.15/0.41  ipcrm: permission denied for id (782139422)
% 0.15/0.41  ipcrm: permission denied for id (785678367)
% 0.15/0.41  ipcrm: permission denied for id (782204960)
% 0.15/0.42  ipcrm: permission denied for id (782270498)
% 0.15/0.42  ipcrm: permission denied for id (782303267)
% 0.22/0.42  ipcrm: permission denied for id (785743908)
% 0.22/0.42  ipcrm: permission denied for id (785776677)
% 0.22/0.42  ipcrm: permission denied for id (782368806)
% 0.22/0.42  ipcrm: permission denied for id (782401575)
% 0.22/0.42  ipcrm: permission denied for id (782434344)
% 0.22/0.43  ipcrm: permission denied for id (782467113)
% 0.22/0.43  ipcrm: permission denied for id (782499882)
% 0.22/0.43  ipcrm: permission denied for id (782532651)
% 0.22/0.43  ipcrm: permission denied for id (782565420)
% 0.22/0.43  ipcrm: permission denied for id (782598189)
% 0.22/0.43  ipcrm: permission denied for id (782630958)
% 0.22/0.43  ipcrm: permission denied for id (785809455)
% 0.22/0.43  ipcrm: permission denied for id (782696496)
% 0.22/0.44  ipcrm: permission denied for id (782729265)
% 0.22/0.44  ipcrm: permission denied for id (785842226)
% 0.22/0.44  ipcrm: permission denied for id (785874995)
% 0.22/0.44  ipcrm: permission denied for id (782827572)
% 0.22/0.44  ipcrm: permission denied for id (782860341)
% 0.22/0.44  ipcrm: permission denied for id (785907766)
% 0.22/0.45  ipcrm: permission denied for id (782958649)
% 0.22/0.45  ipcrm: permission denied for id (783024187)
% 0.22/0.45  ipcrm: permission denied for id (783056956)
% 0.22/0.45  ipcrm: permission denied for id (786038845)
% 0.22/0.45  ipcrm: permission denied for id (786071614)
% 0.22/0.45  ipcrm: permission denied for id (786137152)
% 0.22/0.46  ipcrm: permission denied for id (783253570)
% 0.22/0.46  ipcrm: permission denied for id (786202691)
% 0.22/0.46  ipcrm: permission denied for id (783319108)
% 0.22/0.46  ipcrm: permission denied for id (786268230)
% 0.22/0.46  ipcrm: permission denied for id (786333768)
% 0.22/0.47  ipcrm: permission denied for id (786399305)
% 0.22/0.47  ipcrm: permission denied for id (783482954)
% 0.22/0.47  ipcrm: permission denied for id (783515723)
% 0.22/0.47  ipcrm: permission denied for id (783548492)
% 0.22/0.47  ipcrm: permission denied for id (783581261)
% 0.22/0.47  ipcrm: permission denied for id (783614030)
% 0.22/0.47  ipcrm: permission denied for id (783646799)
% 0.22/0.47  ipcrm: permission denied for id (783679568)
% 0.22/0.48  ipcrm: permission denied for id (783712337)
% 0.22/0.48  ipcrm: permission denied for id (783745106)
% 0.22/0.48  ipcrm: permission denied for id (783777875)
% 0.22/0.48  ipcrm: permission denied for id (783810644)
% 0.22/0.48  ipcrm: permission denied for id (786432085)
% 0.22/0.48  ipcrm: permission denied for id (783876182)
% 0.22/0.48  ipcrm: permission denied for id (786464855)
% 0.22/0.49  ipcrm: permission denied for id (786563162)
% 0.22/0.49  ipcrm: permission denied for id (786595931)
% 0.22/0.49  ipcrm: permission denied for id (784138334)
% 0.22/0.49  ipcrm: permission denied for id (784171103)
% 0.22/0.49  ipcrm: permission denied for id (784203872)
% 0.22/0.50  ipcrm: permission denied for id (784236641)
% 0.22/0.50  ipcrm: permission denied for id (784269410)
% 0.22/0.50  ipcrm: permission denied for id (784302179)
% 0.22/0.50  ipcrm: permission denied for id (784334948)
% 0.22/0.50  ipcrm: permission denied for id (784367717)
% 0.22/0.50  ipcrm: permission denied for id (786727014)
% 0.22/0.50  ipcrm: permission denied for id (784433255)
% 0.22/0.50  ipcrm: permission denied for id (786759784)
% 0.22/0.51  ipcrm: permission denied for id (784498793)
% 0.22/0.51  ipcrm: permission denied for id (784564331)
% 0.22/0.51  ipcrm: permission denied for id (786825324)
% 0.22/0.51  ipcrm: permission denied for id (784629869)
% 0.22/0.51  ipcrm: permission denied for id (784662638)
% 0.22/0.51  ipcrm: permission denied for id (784695407)
% 0.22/0.51  ipcrm: permission denied for id (786858096)
% 0.22/0.52  ipcrm: permission denied for id (786923634)
% 0.22/0.52  ipcrm: permission denied for id (786956403)
% 0.22/0.52  ipcrm: permission denied for id (787021941)
% 0.22/0.52  ipcrm: permission denied for id (787054710)
% 0.22/0.53  ipcrm: permission denied for id (787153017)
% 0.22/0.53  ipcrm: permission denied for id (785088636)
% 0.22/0.53  ipcrm: permission denied for id (785121405)
% 0.22/0.53  ipcrm: permission denied for id (785154174)
% 0.22/0.53  ipcrm: permission denied for id (787251327)
% 0.94/0.66  % (13132)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.94/0.66  % (13145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.94/0.67  % (13122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.68  % (13129)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.69  % (13137)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.69  % (13119)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.70  % (13121)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.70  % (13140)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.70  % (13140)Refutation not found, incomplete strategy% (13140)------------------------------
% 1.31/0.70  % (13140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.70  % (13140)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.70  
% 1.31/0.70  % (13140)Memory used [KB]: 10618
% 1.31/0.70  % (13140)Time elapsed: 0.126 s
% 1.31/0.70  % (13140)------------------------------
% 1.31/0.70  % (13140)------------------------------
% 1.31/0.70  % (13129)Refutation not found, incomplete strategy% (13129)------------------------------
% 1.31/0.70  % (13129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.70  % (13129)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.70  
% 1.31/0.70  % (13129)Memory used [KB]: 10618
% 1.31/0.70  % (13129)Time elapsed: 0.132 s
% 1.31/0.70  % (13129)------------------------------
% 1.31/0.70  % (13129)------------------------------
% 1.31/0.71  % (13135)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.71  % (13120)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.71  % (13120)Refutation not found, incomplete strategy% (13120)------------------------------
% 1.31/0.71  % (13120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.71  % (13120)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.71  
% 1.31/0.71  % (13120)Memory used [KB]: 10618
% 1.31/0.71  % (13120)Time elapsed: 0.126 s
% 1.31/0.71  % (13120)------------------------------
% 1.31/0.71  % (13120)------------------------------
% 1.31/0.71  % (13136)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.72  % (13124)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.72  % (13141)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.72  % (13118)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.72  % (13144)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.72  % (13135)Refutation not found, incomplete strategy% (13135)------------------------------
% 1.31/0.72  % (13135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.72  % (13123)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.72  % (13126)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.72  % (13135)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.72  
% 1.31/0.72  % (13135)Memory used [KB]: 10618
% 1.31/0.72  % (13135)Time elapsed: 0.137 s
% 1.31/0.72  % (13135)------------------------------
% 1.31/0.72  % (13135)------------------------------
% 1.31/0.72  % (13133)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.72  % (13147)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.73  % (13126)Refutation not found, incomplete strategy% (13126)------------------------------
% 1.31/0.73  % (13126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.73  % (13126)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.73  
% 1.31/0.73  % (13126)Memory used [KB]: 10618
% 1.31/0.73  % (13126)Time elapsed: 0.146 s
% 1.31/0.73  % (13128)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.73  % (13126)------------------------------
% 1.31/0.73  % (13126)------------------------------
% 1.31/0.73  % (13128)Refutation not found, incomplete strategy% (13128)------------------------------
% 1.31/0.73  % (13128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.73  % (13128)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.73  
% 1.31/0.73  % (13128)Memory used [KB]: 10618
% 1.31/0.73  % (13128)Time elapsed: 0.154 s
% 1.31/0.73  % (13128)------------------------------
% 1.31/0.73  % (13128)------------------------------
% 1.31/0.73  % (13139)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.73  % (13130)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.74  % (13134)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.74  % (13127)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.74  % (13131)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.74  % (13127)Refutation not found, incomplete strategy% (13127)------------------------------
% 1.31/0.74  % (13127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.74  % (13145)Refutation found. Thanks to Tanya!
% 1.31/0.74  % SZS status Theorem for theBenchmark
% 1.31/0.74  % (13143)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.74  % (13146)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.74  % (13138)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.74  % (13142)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.74/0.74  % (13127)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.74  % (13125)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.74/0.74  
% 1.74/0.74  % (13127)Memory used [KB]: 10618
% 1.74/0.74  % (13127)Time elapsed: 0.162 s
% 1.74/0.74  % (13127)------------------------------
% 1.74/0.74  % (13127)------------------------------
% 1.74/0.75  % SZS output start Proof for theBenchmark
% 1.74/0.75  fof(f942,plain,(
% 1.74/0.75    $false),
% 1.74/0.75    inference(avatar_sat_refutation,[],[f45,f927,f941])).
% 1.74/0.75  fof(f941,plain,(
% 1.74/0.75    spl4_2),
% 1.74/0.75    inference(avatar_contradiction_clause,[],[f938])).
% 1.74/0.75  fof(f938,plain,(
% 1.74/0.75    $false | spl4_2),
% 1.74/0.75    inference(subsumption_resolution,[],[f25,f932])).
% 1.74/0.75  fof(f932,plain,(
% 1.74/0.75    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,sK2))) ) | spl4_2),
% 1.74/0.75    inference(resolution,[],[f928,f27])).
% 1.74/0.75  fof(f27,plain,(
% 1.74/0.75    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f8])).
% 1.74/0.75  fof(f8,axiom,(
% 1.74/0.75    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.74/0.75  fof(f928,plain,(
% 1.74/0.75    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_tarski(sK0,X0)) ) | spl4_2),
% 1.74/0.75    inference(resolution,[],[f44,f35])).
% 1.74/0.75  fof(f35,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f16])).
% 1.74/0.75  fof(f16,plain,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.74/0.75    inference(flattening,[],[f15])).
% 1.74/0.75  fof(f15,plain,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.74/0.75    inference(ennf_transformation,[],[f6])).
% 1.74/0.75  fof(f6,axiom,(
% 1.74/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.74/0.75  fof(f44,plain,(
% 1.74/0.75    ~r1_xboole_0(sK0,sK2) | spl4_2),
% 1.74/0.75    inference(avatar_component_clause,[],[f42])).
% 1.74/0.75  fof(f42,plain,(
% 1.74/0.75    spl4_2 <=> r1_xboole_0(sK0,sK2)),
% 1.74/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.74/0.75  fof(f25,plain,(
% 1.74/0.75    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.74/0.75    inference(cnf_transformation,[],[f20])).
% 1.74/0.75  fof(f20,plain,(
% 1.74/0.75    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.74/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 1.74/0.75  fof(f19,plain,(
% 1.74/0.75    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.74/0.75    introduced(choice_axiom,[])).
% 1.74/0.75  fof(f11,plain,(
% 1.74/0.75    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.74/0.75    inference(ennf_transformation,[],[f10])).
% 1.74/0.75  fof(f10,negated_conjecture,(
% 1.74/0.75    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.74/0.75    inference(negated_conjecture,[],[f9])).
% 1.74/0.75  fof(f9,conjecture,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.74/0.75  fof(f927,plain,(
% 1.74/0.75    spl4_1),
% 1.74/0.75    inference(avatar_contradiction_clause,[],[f926])).
% 1.74/0.75  fof(f926,plain,(
% 1.74/0.75    $false | spl4_1),
% 1.74/0.75    inference(subsumption_resolution,[],[f920,f47])).
% 1.74/0.75  fof(f47,plain,(
% 1.74/0.75    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.74/0.75    inference(duplicate_literal_removal,[],[f46])).
% 1.74/0.75  fof(f46,plain,(
% 1.74/0.75    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.74/0.75    inference(resolution,[],[f32,f31])).
% 1.74/0.75  fof(f31,plain,(
% 1.74/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f24])).
% 1.74/0.75  fof(f24,plain,(
% 1.74/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.74/0.75  fof(f23,plain,(
% 1.74/0.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.74/0.75    introduced(choice_axiom,[])).
% 1.74/0.75  fof(f22,plain,(
% 1.74/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.75    inference(rectify,[],[f21])).
% 1.74/0.75  fof(f21,plain,(
% 1.74/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.75    inference(nnf_transformation,[],[f13])).
% 1.74/0.75  fof(f13,plain,(
% 1.74/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.74/0.75    inference(ennf_transformation,[],[f1])).
% 1.74/0.75  fof(f1,axiom,(
% 1.74/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.74/0.75  fof(f32,plain,(
% 1.74/0.75    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f24])).
% 1.74/0.75  fof(f920,plain,(
% 1.74/0.75    ~r1_tarski(sK1,sK1) | spl4_1),
% 1.74/0.75    inference(resolution,[],[f747,f470])).
% 1.74/0.75  fof(f470,plain,(
% 1.74/0.75    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,sK1)) ) | spl4_1),
% 1.74/0.75    inference(resolution,[],[f460,f452])).
% 1.74/0.75  fof(f452,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2)) )),
% 1.74/0.75    inference(duplicate_literal_removal,[],[f450])).
% 1.74/0.75  fof(f450,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(resolution,[],[f73,f31])).
% 1.74/0.75  fof(f73,plain,(
% 1.74/0.75    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK3(X4,X3),X5) | r1_tarski(X4,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,X2)) )),
% 1.74/0.75    inference(resolution,[],[f48,f30])).
% 1.74/0.75  fof(f30,plain,(
% 1.74/0.75    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f24])).
% 1.74/0.75  fof(f48,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(resolution,[],[f30,f32])).
% 1.74/0.75  fof(f460,plain,(
% 1.74/0.75    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl4_1),
% 1.74/0.75    inference(resolution,[],[f453,f25])).
% 1.74/0.75  fof(f453,plain,(
% 1.74/0.75    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) ) | spl4_1),
% 1.74/0.75    inference(resolution,[],[f452,f40])).
% 1.74/0.75  fof(f40,plain,(
% 1.74/0.75    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.74/0.75    inference(avatar_component_clause,[],[f38])).
% 1.74/0.75  fof(f38,plain,(
% 1.74/0.75    spl4_1 <=> r1_tarski(sK0,sK1)),
% 1.74/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.74/0.75  fof(f747,plain,(
% 1.74/0.75    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 1.74/0.75    inference(subsumption_resolution,[],[f725,f27])).
% 1.74/0.75  fof(f725,plain,(
% 1.74/0.75    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | ~r1_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 1.74/0.75    inference(resolution,[],[f77,f235])).
% 1.74/0.75  fof(f235,plain,(
% 1.74/0.75    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X3)) )),
% 1.74/0.75    inference(subsumption_resolution,[],[f230,f52])).
% 1.74/0.75  fof(f52,plain,(
% 1.74/0.75    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X5)) )),
% 1.74/0.75    inference(superposition,[],[f27,f33])).
% 1.74/0.75  fof(f33,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.74/0.75    inference(cnf_transformation,[],[f4])).
% 1.74/0.75  fof(f4,axiom,(
% 1.74/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.74/0.75  fof(f230,plain,(
% 1.74/0.75    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X2) | r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X2)),X3)) )),
% 1.74/0.75    inference(resolution,[],[f179,f36])).
% 1.74/0.75  fof(f36,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f18])).
% 1.74/0.75  fof(f18,plain,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.74/0.75    inference(flattening,[],[f17])).
% 1.74/0.75  fof(f17,plain,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.74/0.75    inference(ennf_transformation,[],[f7])).
% 1.74/0.75  fof(f7,axiom,(
% 1.74/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.74/0.75  fof(f179,plain,(
% 1.74/0.75    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k2_xboole_0(X7,X6))) )),
% 1.74/0.75    inference(resolution,[],[f98,f52])).
% 1.74/0.75  fof(f98,plain,(
% 1.74/0.75    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X3)) )),
% 1.74/0.75    inference(resolution,[],[f94,f36])).
% 1.74/0.75  fof(f94,plain,(
% 1.74/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 1.74/0.75    inference(superposition,[],[f89,f28])).
% 1.74/0.75  fof(f28,plain,(
% 1.74/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f3])).
% 1.74/0.75  fof(f3,axiom,(
% 1.74/0.75    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.74/0.75  fof(f89,plain,(
% 1.74/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.74/0.75    inference(resolution,[],[f49,f47])).
% 1.74/0.75  fof(f49,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) | r1_tarski(X2,k2_xboole_0(X0,X1))) )),
% 1.74/0.75    inference(superposition,[],[f34,f28])).
% 1.74/0.75  fof(f34,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.74/0.75    inference(cnf_transformation,[],[f14])).
% 1.74/0.75  fof(f14,plain,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.74/0.75    inference(ennf_transformation,[],[f5])).
% 1.74/0.75  fof(f5,axiom,(
% 1.74/0.75    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.74/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.74/0.75  fof(f77,plain,(
% 1.74/0.75    ( ! [X2,X0,X3,X1] : (~r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) | r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_xboole_0(k4_xboole_0(X0,X1),X3)) )),
% 1.74/0.75    inference(superposition,[],[f63,f33])).
% 1.74/0.75  fof(f63,plain,(
% 1.74/0.75    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X2),X1) | r1_tarski(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 1.74/0.75    inference(resolution,[],[f36,f34])).
% 1.74/0.75  fof(f45,plain,(
% 1.74/0.75    ~spl4_1 | ~spl4_2),
% 1.74/0.75    inference(avatar_split_clause,[],[f26,f42,f38])).
% 1.74/0.75  fof(f26,plain,(
% 1.74/0.75    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.74/0.75    inference(cnf_transformation,[],[f20])).
% 1.74/0.75  % SZS output end Proof for theBenchmark
% 1.74/0.75  % (13145)------------------------------
% 1.74/0.75  % (13145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.75  % (13145)Termination reason: Refutation
% 1.74/0.75  
% 1.74/0.75  % (13145)Memory used [KB]: 6780
% 1.74/0.75  % (13145)Time elapsed: 0.096 s
% 1.74/0.75  % (13145)------------------------------
% 1.74/0.75  % (13145)------------------------------
% 1.74/0.75  % (12981)Success in time 0.375 s
%------------------------------------------------------------------------------
