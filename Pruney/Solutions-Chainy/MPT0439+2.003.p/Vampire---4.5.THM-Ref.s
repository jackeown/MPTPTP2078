%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 100 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f37,f40])).

fof(f40,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f17,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl1_1
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f38,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_4
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f36,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_5
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f37,plain,
    ( spl1_5
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f32,f25,f20,f34])).

fof(f20,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f25,plain,
    ( spl1_3
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f32,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f26,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f31,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f27,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f23,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f18,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (792035328)
% 0.13/0.36  ipcrm: permission denied for id (795770882)
% 0.13/0.36  ipcrm: permission denied for id (792068101)
% 0.13/0.36  ipcrm: permission denied for id (792100870)
% 0.21/0.36  ipcrm: permission denied for id (792133639)
% 0.21/0.37  ipcrm: permission denied for id (792166408)
% 0.21/0.37  ipcrm: permission denied for id (792199177)
% 0.21/0.37  ipcrm: permission denied for id (792264715)
% 0.21/0.37  ipcrm: permission denied for id (792330253)
% 0.21/0.37  ipcrm: permission denied for id (798523407)
% 0.21/0.38  ipcrm: permission denied for id (792395792)
% 0.21/0.38  ipcrm: permission denied for id (798588946)
% 0.21/0.38  ipcrm: permission denied for id (792461331)
% 0.21/0.38  ipcrm: permission denied for id (798621716)
% 0.21/0.38  ipcrm: permission denied for id (796098581)
% 0.21/0.38  ipcrm: permission denied for id (796131350)
% 0.21/0.39  ipcrm: permission denied for id (796196888)
% 0.21/0.39  ipcrm: permission denied for id (796295193)
% 0.21/0.39  ipcrm: permission denied for id (796262426)
% 0.21/0.39  ipcrm: permission denied for id (792723484)
% 0.21/0.39  ipcrm: permission denied for id (796360733)
% 0.21/0.39  ipcrm: permission denied for id (792789022)
% 0.21/0.39  ipcrm: permission denied for id (798720031)
% 0.21/0.40  ipcrm: permission denied for id (796557348)
% 0.21/0.40  ipcrm: permission denied for id (796590117)
% 0.21/0.40  ipcrm: permission denied for id (793083943)
% 0.21/0.41  ipcrm: permission denied for id (793116712)
% 0.21/0.41  ipcrm: permission denied for id (793149481)
% 0.21/0.41  ipcrm: permission denied for id (793182250)
% 0.21/0.41  ipcrm: permission denied for id (793215019)
% 0.21/0.41  ipcrm: permission denied for id (793247788)
% 0.21/0.41  ipcrm: permission denied for id (793280557)
% 0.21/0.41  ipcrm: permission denied for id (793313326)
% 0.21/0.41  ipcrm: permission denied for id (798916655)
% 0.21/0.42  ipcrm: permission denied for id (793346096)
% 0.21/0.42  ipcrm: permission denied for id (793378865)
% 0.21/0.42  ipcrm: permission denied for id (793411634)
% 0.21/0.42  ipcrm: permission denied for id (793444403)
% 0.21/0.42  ipcrm: permission denied for id (793477172)
% 0.21/0.42  ipcrm: permission denied for id (793509941)
% 0.21/0.42  ipcrm: permission denied for id (793542710)
% 0.21/0.42  ipcrm: permission denied for id (796688439)
% 0.21/0.43  ipcrm: permission denied for id (798949432)
% 0.21/0.43  ipcrm: permission denied for id (793608249)
% 0.21/0.43  ipcrm: permission denied for id (793641018)
% 0.21/0.43  ipcrm: permission denied for id (798982203)
% 0.21/0.43  ipcrm: permission denied for id (793706556)
% 0.21/0.44  ipcrm: permission denied for id (796885056)
% 0.21/0.44  ipcrm: permission denied for id (799113281)
% 0.21/0.44  ipcrm: permission denied for id (796983363)
% 0.21/0.44  ipcrm: permission denied for id (799178820)
% 0.21/0.44  ipcrm: permission denied for id (797048901)
% 0.21/0.44  ipcrm: permission denied for id (799211590)
% 0.21/0.44  ipcrm: permission denied for id (797114439)
% 0.21/0.45  ipcrm: permission denied for id (799244360)
% 0.21/0.45  ipcrm: permission denied for id (797179977)
% 0.21/0.45  ipcrm: permission denied for id (797245515)
% 0.21/0.45  ipcrm: permission denied for id (797278284)
% 0.21/0.45  ipcrm: permission denied for id (797311053)
% 0.21/0.45  ipcrm: permission denied for id (797343822)
% 0.21/0.46  ipcrm: permission denied for id (797409360)
% 0.21/0.46  ipcrm: permission denied for id (799342673)
% 0.21/0.46  ipcrm: permission denied for id (799375442)
% 0.21/0.46  ipcrm: permission denied for id (797507667)
% 0.21/0.46  ipcrm: permission denied for id (794394709)
% 0.21/0.46  ipcrm: permission denied for id (797573206)
% 0.21/0.47  ipcrm: permission denied for id (799473752)
% 0.21/0.47  ipcrm: permission denied for id (797671513)
% 0.21/0.47  ipcrm: permission denied for id (797704282)
% 0.21/0.47  ipcrm: permission denied for id (797737051)
% 0.21/0.47  ipcrm: permission denied for id (794689630)
% 0.21/0.47  ipcrm: permission denied for id (797835359)
% 0.21/0.47  ipcrm: permission denied for id (794755168)
% 0.21/0.48  ipcrm: permission denied for id (797868129)
% 0.21/0.48  ipcrm: permission denied for id (794787938)
% 0.21/0.48  ipcrm: permission denied for id (794820707)
% 0.21/0.48  ipcrm: permission denied for id (794853476)
% 0.21/0.48  ipcrm: permission denied for id (794886245)
% 0.21/0.48  ipcrm: permission denied for id (794919014)
% 0.21/0.48  ipcrm: permission denied for id (794951783)
% 0.21/0.48  ipcrm: permission denied for id (794984552)
% 0.21/0.49  ipcrm: permission denied for id (797900905)
% 0.21/0.49  ipcrm: permission denied for id (795017322)
% 0.21/0.49  ipcrm: permission denied for id (795050091)
% 0.21/0.49  ipcrm: permission denied for id (795082860)
% 0.21/0.49  ipcrm: permission denied for id (795115629)
% 0.21/0.49  ipcrm: permission denied for id (795148398)
% 0.21/0.49  ipcrm: permission denied for id (795181167)
% 0.21/0.49  ipcrm: permission denied for id (799572080)
% 0.21/0.49  ipcrm: permission denied for id (799604849)
% 0.21/0.50  ipcrm: permission denied for id (799637618)
% 0.21/0.50  ipcrm: permission denied for id (799670387)
% 0.21/0.50  ipcrm: permission denied for id (798130293)
% 0.21/0.50  ipcrm: permission denied for id (798195831)
% 0.21/0.50  ipcrm: permission denied for id (795476088)
% 0.21/0.50  ipcrm: permission denied for id (795508857)
% 0.21/0.51  ipcrm: permission denied for id (795541626)
% 0.21/0.51  ipcrm: permission denied for id (795574395)
% 0.21/0.51  ipcrm: permission denied for id (795607164)
% 0.21/0.51  ipcrm: permission denied for id (799768701)
% 0.21/0.51  ipcrm: permission denied for id (799801470)
% 0.70/0.58  % (13993)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.70/0.58  % (13993)Refutation found. Thanks to Tanya!
% 0.70/0.58  % SZS status Theorem for theBenchmark
% 0.70/0.58  % SZS output start Proof for theBenchmark
% 0.70/0.58  fof(f41,plain,(
% 0.70/0.58    $false),
% 0.70/0.58    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f37,f40])).
% 0.70/0.58  fof(f40,plain,(
% 0.70/0.58    spl1_1 | ~spl1_4 | ~spl1_5),
% 0.70/0.58    inference(avatar_contradiction_clause,[],[f39])).
% 0.70/0.58  fof(f39,plain,(
% 0.70/0.58    $false | (spl1_1 | ~spl1_4 | ~spl1_5)),
% 0.70/0.58    inference(subsumption_resolution,[],[f38,f17])).
% 0.70/0.58  fof(f17,plain,(
% 0.70/0.58    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_1),
% 0.70/0.58    inference(avatar_component_clause,[],[f15])).
% 0.70/0.58  fof(f15,plain,(
% 0.70/0.58    spl1_1 <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.70/0.58  fof(f38,plain,(
% 0.70/0.58    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl1_4 | ~spl1_5)),
% 0.70/0.58    inference(resolution,[],[f36,f30])).
% 0.70/0.58  fof(f30,plain,(
% 0.70/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl1_4),
% 0.70/0.58    inference(avatar_component_clause,[],[f29])).
% 0.70/0.58  fof(f29,plain,(
% 0.70/0.58    spl1_4 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.70/0.58  fof(f36,plain,(
% 0.70/0.58    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_5),
% 0.70/0.58    inference(avatar_component_clause,[],[f34])).
% 0.70/0.58  fof(f34,plain,(
% 0.70/0.58    spl1_5 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.70/0.58  fof(f37,plain,(
% 0.70/0.58    spl1_5 | ~spl1_2 | ~spl1_3),
% 0.70/0.58    inference(avatar_split_clause,[],[f32,f25,f20,f34])).
% 0.70/0.58  fof(f20,plain,(
% 0.70/0.58    spl1_2 <=> v1_relat_1(sK0)),
% 0.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.70/0.58  fof(f25,plain,(
% 0.70/0.58    spl1_3 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.70/0.58  fof(f32,plain,(
% 0.70/0.58    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl1_2 | ~spl1_3)),
% 0.70/0.58    inference(resolution,[],[f26,f22])).
% 0.70/0.58  fof(f22,plain,(
% 0.70/0.58    v1_relat_1(sK0) | ~spl1_2),
% 0.70/0.58    inference(avatar_component_clause,[],[f20])).
% 0.70/0.58  fof(f26,plain,(
% 0.70/0.58    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl1_3),
% 0.70/0.58    inference(avatar_component_clause,[],[f25])).
% 0.70/0.58  fof(f31,plain,(
% 0.70/0.58    spl1_4),
% 0.70/0.58    inference(avatar_split_clause,[],[f13,f29])).
% 0.70/0.58  fof(f13,plain,(
% 0.70/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.70/0.58    inference(cnf_transformation,[],[f7])).
% 0.70/0.58  fof(f7,plain,(
% 0.70/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.70/0.58    inference(ennf_transformation,[],[f1])).
% 0.70/0.58  fof(f1,axiom,(
% 0.70/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.70/0.58  fof(f27,plain,(
% 0.70/0.58    spl1_3),
% 0.70/0.58    inference(avatar_split_clause,[],[f12,f25])).
% 0.70/0.58  fof(f12,plain,(
% 0.70/0.58    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.70/0.58    inference(cnf_transformation,[],[f6])).
% 0.70/0.58  fof(f6,plain,(
% 0.70/0.58    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.70/0.58    inference(ennf_transformation,[],[f2])).
% 0.70/0.58  fof(f2,axiom,(
% 0.70/0.58    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.70/0.58  fof(f23,plain,(
% 0.70/0.58    spl1_2),
% 0.70/0.58    inference(avatar_split_clause,[],[f10,f20])).
% 0.70/0.58  fof(f10,plain,(
% 0.70/0.58    v1_relat_1(sK0)),
% 0.70/0.58    inference(cnf_transformation,[],[f9])).
% 0.70/0.58  fof(f9,plain,(
% 0.70/0.58    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f8])).
% 0.70/0.58  fof(f8,plain,(
% 0.70/0.58    ? [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0 & v1_relat_1(X0)) => (sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.70/0.58    introduced(choice_axiom,[])).
% 0.70/0.58  fof(f5,plain,(
% 0.70/0.58    ? [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0 & v1_relat_1(X0))),
% 0.70/0.58    inference(ennf_transformation,[],[f4])).
% 0.70/0.58  fof(f4,negated_conjecture,(
% 0.70/0.58    ~! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.70/0.58    inference(negated_conjecture,[],[f3])).
% 0.70/0.58  fof(f3,conjecture,(
% 0.70/0.58    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.70/0.58  fof(f18,plain,(
% 0.70/0.58    ~spl1_1),
% 0.70/0.58    inference(avatar_split_clause,[],[f11,f15])).
% 0.70/0.58  fof(f11,plain,(
% 0.70/0.58    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.70/0.58    inference(cnf_transformation,[],[f9])).
% 0.70/0.58  % SZS output end Proof for theBenchmark
% 0.70/0.58  % (13993)------------------------------
% 0.70/0.58  % (13993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.70/0.58  % (13993)Termination reason: Refutation
% 0.70/0.58  
% 0.70/0.58  % (13993)Memory used [KB]: 10490
% 0.70/0.58  % (13993)Time elapsed: 0.005 s
% 0.70/0.58  % (13993)------------------------------
% 0.70/0.58  % (13993)------------------------------
% 0.70/0.58  % (13834)Success in time 0.231 s
%------------------------------------------------------------------------------
