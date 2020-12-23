%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 155 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 435 expanded)
%              Number of equality atoms :   12 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f636,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f282,f595])).

fof(f595,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f19,f500,f520,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f520,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f32,f500,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f500,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f322,f478,f43])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f478,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK9(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f18,f334,f34])).

fof(f334,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK9(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f323,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f323,plain,
    ( ~ r2_hidden(sK9(sK0,sK2),sK2)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl11_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f18,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

% (11984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f322,plain,
    ( r2_hidden(sK9(sK0,sK2),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f282,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f19,f194,f207,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f32,f194,f34])).

fof(f194,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f62,f186,f43])).

fof(f186,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK9(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f18,f70,f34])).

fof(f70,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK9(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f63,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,
    ( ~ r2_hidden(sK9(sK1,sK3),sK3)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f56,f36])).

fof(f56,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl11_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f62,plain,
    ( r2_hidden(sK9(sK1,sK3),sK1)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f56,f35])).

fof(f61,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f17,f58,f54])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11977)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (11973)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11969)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11997)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (11981)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.51  % (11974)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.51  % (11975)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.52  % (11995)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.52  % (11985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.20/0.52  % (11992)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.52  % (11998)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.20/0.52  % (11993)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.20/0.52  % (11973)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f636,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f61,f282,f595])).
% 1.20/0.53  fof(f595,plain,(
% 1.20/0.53    spl11_2),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f577])).
% 1.20/0.53  fof(f577,plain,(
% 1.20/0.53    $false | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f19,f500,f520,f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.20/0.53  fof(f520,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f32,f500,f34])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f15])).
% 1.20/0.53  fof(f15,plain,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.20/0.53  fof(f500,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f322,f478,f43])).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.20/0.53    inference(equality_resolution,[],[f42])).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.20/0.53    inference(equality_resolution,[],[f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f478,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK9(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f18,f334,f34])).
% 1.20/0.53  fof(f334,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK9(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f323,f37])).
% 1.20/0.53  fof(f37,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.20/0.53  fof(f323,plain,(
% 1.20/0.53    ~r2_hidden(sK9(sK0,sK2),sK2) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f60,f36])).
% 1.20/0.53  fof(f36,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f15])).
% 1.20/0.53  fof(f60,plain,(
% 1.20/0.53    ~r1_tarski(sK0,sK2) | spl11_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f58])).
% 1.20/0.53  fof(f58,plain,(
% 1.20/0.53    spl11_2 <=> r1_tarski(sK0,sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.20/0.53  fof(f18,plain,(
% 1.20/0.53    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.20/0.53    inference(cnf_transformation,[],[f13])).
% 1.20/0.53  % (11984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.53  fof(f13,plain,(
% 1.20/0.53    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.20/0.53    inference(flattening,[],[f12])).
% 1.20/0.53  fof(f12,plain,(
% 1.20/0.53    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.20/0.53    inference(ennf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.20/0.53    inference(negated_conjecture,[],[f9])).
% 1.20/0.53  fof(f9,conjecture,(
% 1.20/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.20/0.53  fof(f322,plain,(
% 1.20/0.53    r2_hidden(sK9(sK0,sK2),sK0) | spl11_2),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f60,f35])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK9(X0,X1),X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f15])).
% 1.20/0.53  fof(f19,plain,(
% 1.20/0.53    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f13])).
% 1.20/0.53  fof(f282,plain,(
% 1.20/0.53    spl11_1),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f261])).
% 1.20/0.53  fof(f261,plain,(
% 1.20/0.53    $false | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f19,f194,f207,f21])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f207,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f32,f194,f34])).
% 1.20/0.53  fof(f194,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f62,f186,f43])).
% 1.20/0.53  fof(f186,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK9(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f18,f70,f34])).
% 1.20/0.53  fof(f70,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK9(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f63,f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f7])).
% 1.20/0.53  fof(f63,plain,(
% 1.20/0.53    ~r2_hidden(sK9(sK1,sK3),sK3) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f56,f36])).
% 1.20/0.53  fof(f56,plain,(
% 1.20/0.53    ~r1_tarski(sK1,sK3) | spl11_1),
% 1.20/0.53    inference(avatar_component_clause,[],[f54])).
% 1.20/0.53  fof(f54,plain,(
% 1.20/0.53    spl11_1 <=> r1_tarski(sK1,sK3)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.20/0.53  fof(f62,plain,(
% 1.20/0.53    r2_hidden(sK9(sK1,sK3),sK1) | spl11_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f56,f35])).
% 1.20/0.53  fof(f61,plain,(
% 1.20/0.53    ~spl11_1 | ~spl11_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f17,f58,f54])).
% 1.20/0.53  fof(f17,plain,(
% 1.20/0.53    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.20/0.53    inference(cnf_transformation,[],[f13])).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (11973)------------------------------
% 1.20/0.53  % (11973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (11973)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (11973)Memory used [KB]: 6396
% 1.20/0.53  % (11973)Time elapsed: 0.093 s
% 1.20/0.53  % (11973)------------------------------
% 1.20/0.53  % (11973)------------------------------
% 1.20/0.53  % (11978)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.20/0.53  % (11968)Success in time 0.166 s
%------------------------------------------------------------------------------
