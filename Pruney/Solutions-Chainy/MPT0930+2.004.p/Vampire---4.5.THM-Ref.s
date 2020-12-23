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
% DateTime   : Thu Dec  3 12:59:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 191 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f46,f73,f110,f117,f126])).

fof(f126,plain,
    ( ~ spl4_2
    | spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl4_2
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f35,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f124,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f93,f109])).

fof(f109,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f93,plain,
    ( ! [X2,X3] : ~ r2_hidden(sK1,k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),X3)))
    | spl4_4 ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f62,plain,
    ( ! [X2,X3] : ~ sP3(sK1,k2_zfmisc_1(k1_relat_1(sK0),X2),X3)
    | spl4_4 ),
    inference(resolution,[],[f50,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),X0))
    | spl4_4 ),
    inference(resolution,[],[f45,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f45,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_4
  <=> r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f117,plain,
    ( ~ spl4_2
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f79,f109])).

fof(f79,plain,
    ( ! [X2,X3] : ~ r2_hidden(sK1,k3_xboole_0(X2,k2_zfmisc_1(X3,k2_relat_1(sK0))))
    | spl4_3 ),
    inference(resolution,[],[f54,f25])).

fof(f54,plain,
    ( ! [X2,X3] : ~ sP3(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)),X3)
    | spl4_3 ),
    inference(resolution,[],[f47,f20])).

fof(f47,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k2_zfmisc_1(X0,k2_relat_1(sK0)))
    | spl4_3 ),
    inference(resolution,[],[f41,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_3
  <=> r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f74,f70,f107])).

fof(f70,plain,
    ( spl4_5
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f72,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f28,f70])).

fof(f28,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f37,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f30,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f30,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f46,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f11,f43,f39])).

% (9085)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f11,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (9086)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (9087)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (9086)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (9098)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (9093)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f31,f36,f46,f73,f110,f117,f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~spl4_2 | spl4_4 | ~spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    $false | (~spl4_2 | spl4_4 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    r2_hidden(sK1,sK0) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl4_2 <=> r2_hidden(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0) | (spl4_4 | ~spl4_6)),
% 0.22/0.48    inference(superposition,[],[f93,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl4_6 <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(sK1,k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),X3)))) ) | spl4_4),
% 0.22/0.48    inference(resolution,[],[f62,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~sP3(sK1,k2_zfmisc_1(k1_relat_1(sK0),X2),X3)) ) | spl4_4),
% 0.22/0.48    inference(resolution,[],[f50,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~sP3(X3,X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),X0))) ) | spl4_4),
% 0.22/0.48    inference(resolution,[],[f45,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) | spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl4_4 <=> r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~spl4_2 | spl4_3 | ~spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    $false | (~spl4_2 | spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f35])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0) | (spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(superposition,[],[f79,f109])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(sK1,k3_xboole_0(X2,k2_zfmisc_1(X3,k2_relat_1(sK0))))) ) | spl4_3),
% 0.22/0.48    inference(resolution,[],[f54,f25])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~sP3(sK1,k2_zfmisc_1(X2,k2_relat_1(sK0)),X3)) ) | spl4_3),
% 0.22/0.48    inference(resolution,[],[f47,f20])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK1,k2_zfmisc_1(X0,k2_relat_1(sK0)))) ) | spl4_3),
% 0.22/0.48    inference(resolution,[],[f41,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl4_3 <=> r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl4_6 | ~spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f74,f70,f107])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl4_5 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl4_5),
% 0.22/0.48    inference(resolution,[],[f72,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f70])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl4_5 | ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f28,f70])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    spl4_1 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f30,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v1_relat_1(sK0) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f28])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~spl4_3 | ~spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f11,f43,f39])).
% 0.22/0.48  % (9085)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) | ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f12,f33])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    r2_hidden(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f28])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (9086)------------------------------
% 0.22/0.48  % (9086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9086)Termination reason: Refutation
% 0.22/0.48  % (9090)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  
% 0.22/0.48  % (9086)Memory used [KB]: 10618
% 0.22/0.48  % (9086)Time elapsed: 0.063 s
% 0.22/0.48  % (9086)------------------------------
% 0.22/0.48  % (9086)------------------------------
% 0.22/0.48  % (9100)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (9082)Success in time 0.127 s
%------------------------------------------------------------------------------
