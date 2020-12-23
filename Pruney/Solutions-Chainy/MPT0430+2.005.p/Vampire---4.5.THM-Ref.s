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
% DateTime   : Thu Dec  3 12:46:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  96 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 366 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f56,f63,f71])).

fof(f71,plain,
    ( ~ spl4_2
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl4_2
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f55,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f62,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f62,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f63,plain,
    ( spl4_7
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f59,f40,f28,f61])).

fof(f28,plain,
    ( spl4_1
  <=> v3_setfam_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f40,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( r2_hidden(sK0,sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f29,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f57,plain,
    ( r2_hidden(sK0,sK2)
    | v3_setfam_1(sK2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f23,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f56,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f52,f44,f36,f54])).

fof(f36,plain,
    ( spl4_3
  <=> v3_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f44,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f51,f37])).

fof(f37,plain,
    ( v3_setfam_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f51,plain,
    ( ~ v3_setfam_1(sK1,sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f22,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_setfam_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v3_setfam_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK0)
          & r1_tarski(X2,sK1)
          & v3_setfam_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(X2,sK0)
        & r1_tarski(X2,sK1)
        & v3_setfam_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ v3_setfam_1(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & v3_setfam_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

fof(f42,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f28])).

fof(f21,plain,(
    ~ v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:35:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (10189)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (10171)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.47  % (10189)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f56,f63,f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ~spl4_2 | spl4_6 | ~spl4_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    $false | (~spl4_2 | spl4_6 | ~spl4_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f68,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ~r2_hidden(sK0,sK1) | spl4_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl4_6 <=> r2_hidden(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1) | (~spl4_2 | ~spl4_7)),
% 0.22/0.47    inference(resolution,[],[f64,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl4_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(sK2,X0) | r2_hidden(sK0,X0)) ) | ~spl4_7),
% 0.22/0.47    inference(resolution,[],[f62,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(rectify,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    r2_hidden(sK0,sK2) | ~spl4_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl4_7 <=> r2_hidden(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl4_7 | spl4_1 | ~spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f59,f40,f28,f61])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl4_1 <=> v3_setfam_1(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    r2_hidden(sK0,sK2) | (spl4_1 | ~spl4_4)),
% 0.22/0.47    inference(subsumption_resolution,[],[f57,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ~v3_setfam_1(sK2,sK0) | spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    r2_hidden(sK0,sK2) | v3_setfam_1(sK2,sK0) | ~spl4_4),
% 0.22/0.47    inference(resolution,[],[f23,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(nnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ~spl4_6 | ~spl4_3 | ~spl4_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f44,f36,f54])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl4_3 <=> v3_setfam_1(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ~r2_hidden(sK0,sK1) | (~spl4_3 | ~spl4_5)),
% 0.22/0.47    inference(subsumption_resolution,[],[f51,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    v3_setfam_1(sK1,sK0) | ~spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ~v3_setfam_1(sK1,sK0) | ~r2_hidden(sK0,sK1) | ~spl4_5),
% 0.22/0.47    inference(resolution,[],[f22,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl4_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f44])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(flattening,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : ((~v3_setfam_1(X2,X0) & (r1_tarski(X2,X1) & v3_setfam_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f36])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    v3_setfam_1(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~spl4_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f28])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~v3_setfam_1(sK2,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (10189)------------------------------
% 0.22/0.47  % (10189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (10189)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (10189)Memory used [KB]: 5373
% 0.22/0.47  % (10189)Time elapsed: 0.058 s
% 0.22/0.47  % (10189)------------------------------
% 0.22/0.47  % (10189)------------------------------
% 0.22/0.48  % (10170)Success in time 0.111 s
%------------------------------------------------------------------------------
