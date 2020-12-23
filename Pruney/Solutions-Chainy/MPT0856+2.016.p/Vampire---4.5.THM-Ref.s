%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  157 ( 256 expanded)
%              Number of equality atoms :   36 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f82,f94,f106,f141,f186,f212])).

fof(f212,plain,
    ( spl3_1
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl3_1
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f204,f200])).

fof(f200,plain,
    ( ! [X6] : ~ r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X6,k1_tarski(sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f35,f136])).

fof(f136,plain,
    ( k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_11
  <=> k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f35,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f204,plain,
    ( r2_hidden(k1_mcart_1(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)))
    | spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_6
  <=> r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f186,plain,
    ( ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f48,f171,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f171,plain,
    ( ! [X6] : ~ r2_hidden(k1_mcart_1(sK0),X6)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f158,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f158,plain,
    ( ! [X6] : ~ r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X6,k1_xboole_0))
    | ~ spl3_12 ),
    inference(superposition,[],[f35,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k1_tarski(k1_mcart_1(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_12
  <=> k1_xboole_0 = k1_tarski(k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f48,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f141,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f131,f91,f138,f134])).

fof(f91,plain,
    ( spl3_8
  <=> r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f131,plain,
    ( k1_xboole_0 = k1_tarski(k1_mcart_1(sK0))
    | k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f23,f93])).

fof(f93,plain,
    ( r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f106,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f97,f46,f41])).

fof(f41,plain,
    ( spl3_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f97,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f83,f78,f91])).

fof(f83,plain,
    ( r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f82,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f76,f46,f78])).

fof(f76,plain,
    ( r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f28,f48])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f41,f37])).

fof(f20,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (28518)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.40  % (28518)Refutation not found, incomplete strategy% (28518)------------------------------
% 0.21/0.40  % (28518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (28518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.40  
% 0.21/0.40  % (28518)Memory used [KB]: 1535
% 0.21/0.40  % (28518)Time elapsed: 0.002 s
% 0.21/0.40  % (28518)------------------------------
% 0.21/0.40  % (28518)------------------------------
% 0.21/0.43  % (28521)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (28521)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f213,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f44,f49,f82,f94,f106,f141,f186,f212])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    spl3_1 | ~spl3_6 | ~spl3_11),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_6 | ~spl3_11)),
% 0.21/0.44    inference(subsumption_resolution,[],[f204,f200])).
% 0.21/0.44  fof(f200,plain,(
% 0.21/0.44    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X6,k1_tarski(sK1)))) ) | ~spl3_11),
% 0.21/0.44    inference(superposition,[],[f35,f136])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0)) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f134])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    spl3_11 <=> k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.44    inference(equality_resolution,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.44    inference(nnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))) | (spl3_1 | ~spl3_6)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f80,f39,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    sK1 != k1_mcart_1(sK0) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl3_1 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl3_6 <=> r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ~spl3_3 | ~spl3_12),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    $false | (~spl3_3 | ~spl3_12)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f48,f171,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),X6)) ) | ~spl3_12),
% 0.21/0.44    inference(forward_demodulation,[],[f158,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X6,k1_xboole_0))) ) | ~spl3_12),
% 0.21/0.44    inference(superposition,[],[f35,f140])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tarski(k1_mcart_1(sK0)) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl3_12 <=> k1_xboole_0 = k1_tarski(k1_mcart_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl3_11 | spl3_12 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f131,f91,f138,f134])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl3_8 <=> r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tarski(k1_mcart_1(sK0)) | k1_tarski(sK1) = k1_tarski(k1_mcart_1(sK0)) | ~spl3_8),
% 0.21/0.44    inference(resolution,[],[f23,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1)) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl3_2 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f97,f46,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_2 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl3_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f48,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl3_8 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f83,f78,f91])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    r1_tarski(k1_tarski(k1_mcart_1(sK0)),k1_tarski(sK1)) | ~spl3_6),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f80,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(resolution,[],[f22,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl3_6 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f76,f46,f78])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) | ~spl3_3),
% 0.21/0.44    inference(resolution,[],[f28,f48])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f41,f37])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (28521)------------------------------
% 0.21/0.44  % (28521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (28521)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (28521)Memory used [KB]: 10746
% 0.21/0.44  % (28521)Time elapsed: 0.040 s
% 0.21/0.44  % (28521)------------------------------
% 0.21/0.44  % (28521)------------------------------
% 0.21/0.44  % (28504)Success in time 0.093 s
%------------------------------------------------------------------------------
