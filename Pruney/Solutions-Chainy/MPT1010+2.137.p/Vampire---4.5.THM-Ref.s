%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 146 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 359 expanded)
%              Number of equality atoms :   55 ( 154 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f73,f78,f85,f135,f168,f311,f332])).

fof(f332,plain,
    ( ~ spl6_12
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl6_12
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f310,f234,f310,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f234,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl6_12 ),
    inference(superposition,[],[f207,f207])).

fof(f207,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X0 )
    | ~ spl6_12 ),
    inference(superposition,[],[f177,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f177,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3)
        | k1_xboole_0 = X3 )
    | ~ spl6_12 ),
    inference(superposition,[],[f43,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_12
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f310,plain,
    ( k1_xboole_0 != sK1
    | spl6_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f311,plain,
    ( ~ spl6_17
    | spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f218,f129,f70,f308])).

fof(f70,plain,
    ( spl6_4
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f218,plain,
    ( k1_xboole_0 != sK1
    | spl6_4
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f72,f207])).

fof(f72,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f168,plain,
    ( ~ spl6_2
    | spl6_4
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl6_2
    | spl6_4
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f61,f72,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_13 ),
    inference(resolution,[],[f134,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f61,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f135,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f86,f82,f75,f54,f133,f129])).

fof(f54,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f75,plain,
    ( spl6_5
  <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f82,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f20,f39])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f78,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f19,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f18,f54])).

fof(f18,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (12785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (12795)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (12797)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12789)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (12785)Refutation not found, incomplete strategy% (12785)------------------------------
% 0.20/0.51  % (12785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12785)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12785)Memory used [KB]: 10746
% 0.20/0.51  % (12785)Time elapsed: 0.102 s
% 0.20/0.51  % (12785)------------------------------
% 0.20/0.51  % (12785)------------------------------
% 0.20/0.52  % (12797)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f57,f62,f73,f78,f85,f135,f168,f311,f332])).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    ~spl6_12 | spl6_17),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f319])).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    $false | (~spl6_12 | spl6_17)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f310,f234,f310,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1) ) | ~spl6_12),
% 0.20/0.52    inference(superposition,[],[f207,f207])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl6_12),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f205])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0) ) | ~spl6_12),
% 0.20/0.52    inference(superposition,[],[f177,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ( ! [X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3) | k1_xboole_0 = X3) ) | ~spl6_12),
% 0.20/0.52    inference(superposition,[],[f43,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl6_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl6_12 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.52  fof(f310,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl6_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f308])).
% 0.20/0.52  fof(f308,plain,(
% 0.20/0.52    spl6_17 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    ~spl6_17 | spl6_4 | ~spl6_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f218,f129,f70,f308])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    spl6_4 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | (spl6_4 | ~spl6_12)),
% 0.20/0.52    inference(backward_demodulation,[],[f72,f207])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    sK1 != k1_funct_1(sK3,sK2) | spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f70])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ~spl6_2 | spl6_4 | ~spl6_13),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f163])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    $false | (~spl6_2 | spl6_4 | ~spl6_13)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f61,f72,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl6_13),
% 0.20/0.52    inference(resolution,[],[f134,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f39])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl6_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl6_13 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl6_12 | spl6_13 | ~spl6_1 | ~spl6_5 | ~spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f86,f82,f75,f54,f133,f129])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl6_1 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl6_5 <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))) ) | ~spl6_6),
% 0.20/0.52    inference(resolution,[],[f84,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~spl6_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f82])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f82])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 0.20/0.52    inference(definition_unfolding,[],[f20,f39])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f75])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.52    inference(definition_unfolding,[],[f19,f39])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ~spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f70])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    sK1 != k1_funct_1(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f59])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f18,f54])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    v1_funct_1(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (12797)------------------------------
% 0.20/0.52  % (12797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12797)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (12797)Memory used [KB]: 10874
% 0.20/0.52  % (12797)Time elapsed: 0.060 s
% 0.20/0.52  % (12797)------------------------------
% 0.20/0.52  % (12797)------------------------------
% 1.24/0.52  % (12774)Success in time 0.16 s
%------------------------------------------------------------------------------
