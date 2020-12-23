%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  56 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 126 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f92,f93,f111])).

fof(f111,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f102,f20])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f102,plain,
    ( ! [X1] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X1))
    | ~ spl3_6 ),
    inference(superposition,[],[f31,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f31,plain,(
    ! [X0] : ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f18,f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f18,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f93,plain,
    ( ~ spl3_2
    | spl3_6 ),
    inference(avatar_split_clause,[],[f65,f89,f27])).

fof(f27,plain,
    ( spl3_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | sK0 != k1_mcart_1(sK0) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f32,plain,(
    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f92,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f66,f89,f23])).

fof(f23,plain,
    ( spl3_1
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | sK0 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f14,f27,f23])).

fof(f14,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (20299)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (20311)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (20299)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f30,f92,f93,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~spl3_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    $false | ~spl3_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X1))) ) | ~spl3_6),
% 0.21/0.49    inference(superposition,[],[f31,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_6 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f18,f15,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~spl3_2 | spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f89,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    spl3_2 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | sK0 != k1_mcart_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f32,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_mcart_1(X2) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f15,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~spl3_1 | spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f89,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    spl3_1 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | sK0 != k2_mcart_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f32,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_mcart_1(X2) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    spl3_1 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f27,f23])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20299)------------------------------
% 0.21/0.50  % (20299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20299)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20299)Memory used [KB]: 10746
% 0.21/0.50  % (20299)Time elapsed: 0.067 s
% 0.21/0.50  % (20299)------------------------------
% 0.21/0.50  % (20299)------------------------------
% 0.21/0.50  % (20289)Success in time 0.131 s
%------------------------------------------------------------------------------
