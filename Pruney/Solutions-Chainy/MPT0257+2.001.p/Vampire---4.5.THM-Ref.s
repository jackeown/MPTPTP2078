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
% DateTime   : Thu Dec  3 12:40:02 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   50 (  78 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  126 ( 170 expanded)
%              Number of equality atoms :   53 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f110,f122,f135,f136])).

fof(f136,plain,
    ( sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f135,plain,
    ( ~ spl5_1
    | ~ spl5_7
    | spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f130,f119,f85,f132,f80])).

fof(f80,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f132,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f85,plain,
    ( spl5_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f119,plain,
    ( spl5_6
  <=> sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f89,f121])).

fof(f121,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK0,sK0))
        | k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),X0)
        | ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),sK1) )
    | spl5_2 ),
    inference(superposition,[],[f87,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f87,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f122,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f115,f107,f119])).

fof(f107,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f115,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f109,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f109,plain,
    ( r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f104,f85,f107])).

fof(f104,plain,
    ( r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_2 ),
    inference(factoring,[],[f91])).

fof(f91,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),X2)
        | k2_enumset1(sK0,sK0,sK0,sK0) != X2 )
    | spl5_2 ),
    inference(superposition,[],[f87,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f16,f46,f21,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f83,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f15,f80])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (812843009)
% 0.12/0.36  ipcrm: permission denied for id (812875778)
% 0.12/0.36  ipcrm: permission denied for id (812908547)
% 0.20/0.36  ipcrm: permission denied for id (812974086)
% 0.20/0.36  ipcrm: permission denied for id (813006855)
% 0.20/0.37  ipcrm: permission denied for id (813039625)
% 0.20/0.37  ipcrm: permission denied for id (813072394)
% 0.20/0.37  ipcrm: permission denied for id (813137932)
% 0.20/0.37  ipcrm: permission denied for id (813170703)
% 0.20/0.38  ipcrm: permission denied for id (813367318)
% 0.20/0.38  ipcrm: permission denied for id (813400087)
% 0.20/0.38  ipcrm: permission denied for id (813596703)
% 0.20/0.38  ipcrm: permission denied for id (813629473)
% 0.20/0.39  ipcrm: permission denied for id (813826088)
% 0.20/0.39  ipcrm: permission denied for id (813858857)
% 0.20/0.39  ipcrm: permission denied for id (813891626)
% 0.20/0.40  ipcrm: permission denied for id (814088242)
% 0.20/0.40  ipcrm: permission denied for id (814219320)
% 0.20/0.40  ipcrm: permission denied for id (814317627)
% 0.20/0.41  ipcrm: permission denied for id (814383165)
% 0.20/0.41  ipcrm: permission denied for id (814448703)
% 0.20/0.41  ipcrm: permission denied for id (814481472)
% 0.20/0.41  ipcrm: permission denied for id (814579779)
% 0.20/0.41  ipcrm: permission denied for id (814612548)
% 0.20/0.42  ipcrm: permission denied for id (814743626)
% 0.20/0.42  ipcrm: permission denied for id (814776395)
% 0.20/0.42  ipcrm: permission denied for id (814809165)
% 0.20/0.42  ipcrm: permission denied for id (814841934)
% 0.20/0.42  ipcrm: permission denied for id (814874703)
% 0.20/0.42  ipcrm: permission denied for id (814907472)
% 0.20/0.42  ipcrm: permission denied for id (814940241)
% 0.20/0.42  ipcrm: permission denied for id (815005779)
% 0.20/0.42  ipcrm: permission denied for id (815071317)
% 0.20/0.43  ipcrm: permission denied for id (815169624)
% 0.20/0.43  ipcrm: permission denied for id (815202394)
% 0.20/0.43  ipcrm: permission denied for id (815300701)
% 0.20/0.43  ipcrm: permission denied for id (815366241)
% 0.20/0.44  ipcrm: permission denied for id (815431779)
% 0.20/0.44  ipcrm: permission denied for id (815562857)
% 0.20/0.44  ipcrm: permission denied for id (815693933)
% 0.20/0.45  ipcrm: permission denied for id (815759471)
% 0.20/0.45  ipcrm: permission denied for id (815857779)
% 0.20/0.45  ipcrm: permission denied for id (815923317)
% 0.20/0.45  ipcrm: permission denied for id (816087162)
% 0.20/0.46  ipcrm: permission denied for id (816185469)
% 0.20/0.46  ipcrm: permission denied for id (816251007)
% 0.85/0.57  % (15905)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.02/0.59  % (15898)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.02/0.60  % (15920)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.02/0.60  % (15904)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.02/0.60  % (15909)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.02/0.61  % (15912)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.02/0.61  % (15897)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.02/0.61  % (15918)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.02/0.61  % (15910)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.02/0.62  % (15924)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.02/0.62  % (15914)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.02/0.62  % (15899)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.02/0.62  % (15918)Refutation found. Thanks to Tanya!
% 1.02/0.62  % SZS status Theorem for theBenchmark
% 1.02/0.62  % SZS output start Proof for theBenchmark
% 1.02/0.62  fof(f137,plain,(
% 1.02/0.62    $false),
% 1.02/0.62    inference(avatar_sat_refutation,[],[f83,f88,f110,f122,f135,f136])).
% 1.02/0.62  fof(f136,plain,(
% 1.02/0.62    sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.02/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.02/0.62  fof(f135,plain,(
% 1.02/0.62    ~spl5_1 | ~spl5_7 | spl5_2 | ~spl5_6),
% 1.02/0.62    inference(avatar_split_clause,[],[f130,f119,f85,f132,f80])).
% 1.02/0.62  fof(f80,plain,(
% 1.02/0.62    spl5_1 <=> r2_hidden(sK0,sK1)),
% 1.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.02/0.62  fof(f132,plain,(
% 1.02/0.62    spl5_7 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.02/0.62  fof(f85,plain,(
% 1.02/0.62    spl5_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.02/0.62  fof(f119,plain,(
% 1.02/0.62    spl5_6 <=> sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.02/0.62  fof(f130,plain,(
% 1.02/0.62    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl5_2 | ~spl5_6)),
% 1.02/0.62    inference(trivial_inequality_removal,[],[f129])).
% 1.02/0.62  fof(f129,plain,(
% 1.02/0.62    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK1) | (spl5_2 | ~spl5_6)),
% 1.02/0.62    inference(duplicate_literal_removal,[],[f123])).
% 1.02/0.62  fof(f123,plain,(
% 1.02/0.62    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl5_2 | ~spl5_6)),
% 1.02/0.62    inference(superposition,[],[f89,f121])).
% 1.02/0.62  fof(f121,plain,(
% 1.02/0.62    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 1.02/0.62    inference(avatar_component_clause,[],[f119])).
% 1.02/0.62  fof(f89,plain,(
% 1.02/0.62    ( ! [X0] : (~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),X0) | ~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),sK1)) ) | spl5_2),
% 1.02/0.62    inference(superposition,[],[f87,f57])).
% 1.02/0.62  fof(f57,plain,(
% 1.02/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 1.02/0.62    inference(definition_unfolding,[],[f31,f21])).
% 1.02/0.62  fof(f21,plain,(
% 1.02/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.02/0.62    inference(cnf_transformation,[],[f5])).
% 1.02/0.62  fof(f5,axiom,(
% 1.02/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.02/0.62  fof(f31,plain,(
% 1.02/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.02/0.62    inference(cnf_transformation,[],[f2])).
% 1.02/0.62  fof(f2,axiom,(
% 1.02/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.02/0.62  fof(f87,plain,(
% 1.02/0.62    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_2),
% 1.02/0.62    inference(avatar_component_clause,[],[f85])).
% 1.02/0.62  fof(f122,plain,(
% 1.02/0.62    spl5_6 | ~spl5_5),
% 1.02/0.62    inference(avatar_split_clause,[],[f115,f107,f119])).
% 1.02/0.62  fof(f107,plain,(
% 1.02/0.62    spl5_5 <=> r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.02/0.62  fof(f115,plain,(
% 1.02/0.62    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 1.02/0.62    inference(duplicate_literal_removal,[],[f114])).
% 1.02/0.62  fof(f114,plain,(
% 1.02/0.62    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 1.02/0.62    inference(resolution,[],[f109,f78])).
% 1.02/0.62  fof(f78,plain,(
% 1.02/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.02/0.62    inference(equality_resolution,[],[f61])).
% 1.02/0.62  fof(f61,plain,(
% 1.02/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.02/0.62    inference(definition_unfolding,[],[f41,f24])).
% 1.02/0.62  fof(f24,plain,(
% 1.02/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.02/0.62    inference(cnf_transformation,[],[f9])).
% 1.02/0.62  fof(f9,axiom,(
% 1.02/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.02/0.62  fof(f41,plain,(
% 1.02/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.02/0.62    inference(cnf_transformation,[],[f14])).
% 1.02/0.62  fof(f14,plain,(
% 1.02/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.02/0.62    inference(ennf_transformation,[],[f6])).
% 1.02/0.62  fof(f6,axiom,(
% 1.02/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.02/0.62  fof(f109,plain,(
% 1.02/0.62    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 1.02/0.62    inference(avatar_component_clause,[],[f107])).
% 1.02/0.62  fof(f110,plain,(
% 1.02/0.62    spl5_5 | spl5_2),
% 1.02/0.62    inference(avatar_split_clause,[],[f104,f85,f107])).
% 1.02/0.62  fof(f104,plain,(
% 1.02/0.62    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_2),
% 1.02/0.62    inference(trivial_inequality_removal,[],[f103])).
% 1.02/0.62  fof(f103,plain,(
% 1.02/0.62    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_2),
% 1.02/0.62    inference(factoring,[],[f91])).
% 1.02/0.62  fof(f91,plain,(
% 1.02/0.62    ( ! [X2] : (r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),X2) | k2_enumset1(sK0,sK0,sK0,sK0) != X2) ) | spl5_2),
% 1.02/0.62    inference(superposition,[],[f87,f55])).
% 1.02/0.62  fof(f55,plain,(
% 1.02/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 1.02/0.62    inference(definition_unfolding,[],[f33,f21])).
% 1.02/0.62  fof(f33,plain,(
% 1.02/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.02/0.62    inference(cnf_transformation,[],[f2])).
% 1.02/0.62  fof(f88,plain,(
% 1.02/0.62    ~spl5_2),
% 1.02/0.62    inference(avatar_split_clause,[],[f47,f85])).
% 1.02/0.62  fof(f47,plain,(
% 1.02/0.62    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.02/0.62    inference(definition_unfolding,[],[f16,f46,f21,f46])).
% 1.02/0.62  fof(f46,plain,(
% 1.02/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.02/0.62    inference(definition_unfolding,[],[f17,f45])).
% 1.02/0.62  fof(f45,plain,(
% 1.02/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.02/0.62    inference(definition_unfolding,[],[f20,f24])).
% 1.02/0.62  fof(f20,plain,(
% 1.02/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.02/0.62    inference(cnf_transformation,[],[f8])).
% 1.02/0.62  fof(f8,axiom,(
% 1.02/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.02/0.62  fof(f17,plain,(
% 1.02/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.02/0.62    inference(cnf_transformation,[],[f7])).
% 1.02/0.62  fof(f7,axiom,(
% 1.02/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.02/0.62  fof(f16,plain,(
% 1.02/0.62    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.02/0.62    inference(cnf_transformation,[],[f13])).
% 1.02/0.62  fof(f13,plain,(
% 1.02/0.62    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 1.02/0.62    inference(ennf_transformation,[],[f12])).
% 1.02/0.62  fof(f12,negated_conjecture,(
% 1.02/0.62    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.02/0.62    inference(negated_conjecture,[],[f11])).
% 1.02/0.62  fof(f11,conjecture,(
% 1.02/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 1.02/0.62  fof(f83,plain,(
% 1.02/0.62    spl5_1),
% 1.02/0.62    inference(avatar_split_clause,[],[f15,f80])).
% 1.02/0.62  fof(f15,plain,(
% 1.02/0.62    r2_hidden(sK0,sK1)),
% 1.02/0.62    inference(cnf_transformation,[],[f13])).
% 1.02/0.62  % SZS output end Proof for theBenchmark
% 1.02/0.62  % (15918)------------------------------
% 1.02/0.62  % (15918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.02/0.62  % (15918)Termination reason: Refutation
% 1.02/0.62  
% 1.02/0.62  % (15918)Memory used [KB]: 10746
% 1.02/0.62  % (15918)Time elapsed: 0.075 s
% 1.02/0.62  % (15918)------------------------------
% 1.02/0.62  % (15918)------------------------------
% 1.02/0.62  % (15922)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.02/0.62  % (15901)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.02/0.62  % (15900)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.02/0.62  % (15896)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.02/0.63  % (15762)Success in time 0.272 s
%------------------------------------------------------------------------------
