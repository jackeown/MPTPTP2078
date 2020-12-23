%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  86 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 184 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f48,f64,f67,f69])).

fof(f69,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK2(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f43,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_xboole_0))
    | ~ spl4_3 ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f60,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_6
  <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f67,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f65,f62,f31])).

fof(f31,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( spl4_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(resolution,[],[f63,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f63,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f57,f35,f62,f59])).

fof(f35,plain,
    ( spl4_2
  <=> r1_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK3(k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,
    ( r1_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK3(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK3(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f48,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f44,f39,f46])).

fof(f44,plain,
    ( k1_xboole_0 = sK2(k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f43,f26])).

fof(f41,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f31])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (8468)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.45  % (8468)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % (8477)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f33,f37,f41,f48,f64,f67,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ~spl4_3 | ~spl4_4 | ~spl4_6),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    $false | (~spl4_3 | ~spl4_4 | ~spl4_6)),
% 0.20/0.45    inference(resolution,[],[f60,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_3 | ~spl4_4)),
% 0.20/0.45    inference(superposition,[],[f43,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    k1_xboole_0 = sK2(k1_xboole_0) | ~spl4_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    spl4_4 <=> k1_xboole_0 = sK2(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,sK2(k1_xboole_0))) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f42,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0] : ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f29,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~spl4_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl4_6 <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    spl4_1 | ~spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f65,f62,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    spl4_1 <=> k1_xboole_0 = sK0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    spl4_7 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    k1_xboole_0 = sK0 | ~spl4_7),
% 0.20/0.45    inference(resolution,[],[f63,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl4_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f62])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    spl4_6 | spl4_7 | ~spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f57,f35,f62,f59])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl4_2 <=> r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK3(k1_xboole_0),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.45    inference(resolution,[],[f28,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    r1_setfam_1(sK0,k1_xboole_0) | ~spl4_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f35])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK3(X1),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK3(X1),X1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl4_4 | ~spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f44,f39,f46])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    k1_xboole_0 = sK2(k1_xboole_0) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f43,f26])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f39])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f23,f35])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f24,f31])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    k1_xboole_0 != sK0),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (8468)------------------------------
% 0.20/0.45  % (8468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (8468)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (8468)Memory used [KB]: 10618
% 0.20/0.45  % (8468)Time elapsed: 0.056 s
% 0.20/0.45  % (8468)------------------------------
% 0.20/0.45  % (8468)------------------------------
% 0.20/0.46  % (8461)Success in time 0.1 s
%------------------------------------------------------------------------------
