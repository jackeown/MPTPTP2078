%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 117 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 330 expanded)
%              Number of equality atoms :   35 ( 101 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f86,f93,f96])).

% (31213)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f96,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f92,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(X0,sK0,sK0),k1_xboole_0)
        | k1_xboole_0 != X0 )
    | spl3_1 ),
    inference(superposition,[],[f70,f10])).

fof(f10,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f70,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3)
        | k1_xboole_0 != k4_xboole_0(X2,X3) )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3)
        | k1_xboole_0 != k4_xboole_0(X2,X3)
        | ~ r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3) )
    | spl3_1 ),
    inference(resolution,[],[f59,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f59,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),k4_xboole_0(X1,X2))
        | ~ r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),X2)
        | k1_xboole_0 != k4_xboole_0(X1,X2) )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k4_xboole_0(X1,X2)
        | ~ r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),X2)
        | k1_xboole_0 != k4_xboole_0(X1,X2)
        | r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),k4_xboole_0(X1,X2)) )
    | spl3_1 ),
    inference(resolution,[],[f42,f40])).

fof(f40,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0,sK0,sK0),sK0)
        | k1_xboole_0 != X0
        | r2_hidden(sK1(X0,sK0,sK0),X0) )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(sK1(X0,sK0,sK0),sK0)
        | r2_hidden(sK1(X0,sK0,sK0),X0)
        | r2_hidden(sK1(X0,sK0,sK0),sK0) )
    | spl3_1 ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

% (31212)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | k5_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f33,plain,
    ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),sK0)
        | k1_xboole_0 != k4_xboole_0(X2,X3)
        | ~ r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3) )
    | spl3_1 ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(X1,sK0,sK0),X1)
        | ~ r2_hidden(sK1(X1,sK0,sK0),sK0)
        | k1_xboole_0 != X1 )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK1(X1,sK0,sK0),sK0)
        | r2_hidden(sK1(X1,sK0,sK0),X1)
        | ~ r2_hidden(sK1(X1,sK0,sK0),sK0) )
    | spl3_1 ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | k5_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_5
  <=> r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,
    ( spl3_5
    | spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f88,f83,f31,f90])).

fof(f83,plain,
    ( spl3_4
  <=> r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0)
    | spl3_1
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0)
    | spl3_1
    | spl3_4 ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f81,f31,f83])).

fof(f81,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0)
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0)
    | k1_xboole_0 != k1_xboole_0
    | spl3_1 ),
    inference(resolution,[],[f74,f39])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f31])).

fof(f22,plain,(
    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) ),
    inference(definition_unfolding,[],[f9,f11])).

fof(f9,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (31233)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (31225)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (31239)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (31215)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31215)Refutation not found, incomplete strategy% (31215)------------------------------
% 0.21/0.51  % (31215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31215)Memory used [KB]: 6140
% 0.21/0.51  % (31215)Time elapsed: 0.100 s
% 0.21/0.51  % (31215)------------------------------
% 0.21/0.51  % (31215)------------------------------
% 0.21/0.51  % (31217)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31233)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f34,f86,f93,f96])).
% 0.21/0.51  % (31213)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_1 | ~spl3_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    $false | (spl3_1 | ~spl3_5)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_5)),
% 0.21/0.51    inference(resolution,[],[f92,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK1(X0,sK0,sK0),k1_xboole_0) | k1_xboole_0 != X0) ) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f70,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3) | k1_xboole_0 != k4_xboole_0(X2,X3)) ) | spl3_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3) | k1_xboole_0 != k4_xboole_0(X2,X3) | ~r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3)) ) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f59,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),k4_xboole_0(X1,X2)) | ~r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),X2) | k1_xboole_0 != k4_xboole_0(X1,X2)) ) | spl3_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(X1,X2) | ~r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),X2) | k1_xboole_0 != k4_xboole_0(X1,X2) | r2_hidden(sK1(k4_xboole_0(X1,X2),sK0,sK0),k4_xboole_0(X1,X2))) ) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f42,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(X0,sK0,sK0),sK0) | k1_xboole_0 != X0 | r2_hidden(sK1(X0,sK0,sK0),X0)) ) | spl3_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK1(X0,sK0,sK0),sK0) | r2_hidden(sK1(X0,sK0,sK0),X0) | r2_hidden(sK1(X0,sK0,sK0),sK0)) ) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f33,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f12,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  % (31212)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | k5_xboole_0(X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ? [X3] : (~r2_hidden(X3,X0) <~> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    spl3_1 <=> k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),sK0) | k1_xboole_0 != k4_xboole_0(X2,X3) | ~r2_hidden(sK1(k4_xboole_0(X2,X3),sK0,sK0),X3)) ) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f39,f28])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK1(X1,sK0,sK0),X1) | ~r2_hidden(sK1(X1,sK0,sK0),sK0) | k1_xboole_0 != X1) ) | spl3_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK1(X1,sK0,sK0),sK0) | r2_hidden(sK1(X1,sK0,sK0),X1) | ~r2_hidden(sK1(X1,sK0,sK0),sK0)) ) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f33,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X0 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f11])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | k5_xboole_0(X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_5 <=> r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl3_5 | spl3_1 | spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f83,f31,f90])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_4 <=> r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0) | (spl3_1 | spl3_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK1(k1_xboole_0,sK0,sK0),k1_xboole_0) | (spl3_1 | spl3_4)),
% 0.21/0.51    inference(resolution,[],[f85,f40])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0) | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~spl3_4 | spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f31,f83])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0) | spl3_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0) | spl3_1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1(k1_xboole_0,sK0,sK0),sK0) | k1_xboole_0 != k1_xboole_0 | spl3_1),
% 0.21/0.51    inference(resolution,[],[f74,f39])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f31])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))),
% 0.21/0.51    inference(definition_unfolding,[],[f9,f11])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31233)------------------------------
% 0.21/0.51  % (31233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31233)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31233)Memory used [KB]: 10746
% 0.21/0.51  % (31233)Time elapsed: 0.059 s
% 0.21/0.51  % (31233)------------------------------
% 0.21/0.51  % (31233)------------------------------
% 0.21/0.51  % (31231)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (31223)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31210)Success in time 0.157 s
%------------------------------------------------------------------------------
