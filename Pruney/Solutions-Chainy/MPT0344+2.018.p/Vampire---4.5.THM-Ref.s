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
% DateTime   : Thu Dec  3 12:43:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 243 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f47,f54,f62,f77,f265])).

fof(f265,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_6 ),
    inference(subsumption_resolution,[],[f249,f38])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f249,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f70,f53,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f53,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_4
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_6
  <=> r2_hidden(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f77,plain,
    ( ~ spl3_6
    | spl3_5 ),
    inference(avatar_split_clause,[],[f66,f59,f68])).

fof(f59,plain,
    ( spl3_5
  <=> m1_subset_1(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | spl3_5 ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,
    ( ~ m1_subset_1(sK2(sK1),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f62,plain,
    ( ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f51,f59])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2(sK1),sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f54,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f48,f44,f51])).

fof(f44,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f41,f31,f44])).

fof(f31,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f33,f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.42  % (31140)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.42  % (31140)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f267,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f34,f39,f47,f54,f62,f77,f265])).
% 0.19/0.42  fof(f265,plain,(
% 0.19/0.42    ~spl3_2 | ~spl3_4 | spl3_6),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f264])).
% 0.19/0.42  fof(f264,plain,(
% 0.19/0.42    $false | (~spl3_2 | ~spl3_4 | spl3_6)),
% 0.19/0.42    inference(subsumption_resolution,[],[f249,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.42  fof(f249,plain,(
% 0.19/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_4 | spl3_6)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f53,f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    r2_hidden(sK2(sK1),sK1) | ~spl3_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f51])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    spl3_4 <=> r2_hidden(sK2(sK1),sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    ~r2_hidden(sK2(sK1),sK0) | spl3_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f68])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    spl3_6 <=> r2_hidden(sK2(sK1),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    ~spl3_6 | spl3_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f66,f59,f68])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    spl3_5 <=> m1_subset_1(sK2(sK1),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    ~r2_hidden(sK2(sK1),sK0) | spl3_5),
% 0.19/0.42    inference(resolution,[],[f40,f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    ~m1_subset_1(sK2(sK1),sK0) | spl3_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f59])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f26,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(rectify,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    ~spl3_5 | ~spl3_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f55,f51,f59])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ~m1_subset_1(sK2(sK1),sK0) | ~spl3_4),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f53,f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(flattening,[],[f7])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    spl3_4 | spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f48,f44,f51])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl3_3 <=> v1_xboole_0(sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    r2_hidden(sK2(sK1),sK1) | spl3_3),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f46,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ~v1_xboole_0(sK1) | spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f44])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ~spl3_3 | spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f41,f31,f44])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    spl3_1 <=> k1_xboole_0 = sK1),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ~v1_xboole_0(sK1) | spl3_1),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f33,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    k1_xboole_0 != sK1 | spl3_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f31])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f19,f36])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ~spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f20,f31])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    k1_xboole_0 != sK1),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (31140)------------------------------
% 0.19/0.42  % (31140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (31140)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (31140)Memory used [KB]: 10746
% 0.19/0.42  % (31140)Time elapsed: 0.008 s
% 0.19/0.42  % (31140)------------------------------
% 0.19/0.42  % (31140)------------------------------
% 0.19/0.43  % (31122)Success in time 0.084 s
%------------------------------------------------------------------------------
