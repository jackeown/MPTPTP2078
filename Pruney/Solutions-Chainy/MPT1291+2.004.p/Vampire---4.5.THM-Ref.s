%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  97 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :    5
%              Number of atoms          :  172 ( 263 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f56,f60,f71,f80,f90,f107,f115,f130,f136])).

fof(f136,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | spl4_22 ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6
    | spl4_22 ),
    inference(resolution,[],[f129,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_22
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f130,plain,
    ( ~ spl4_22
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f120,f113,f30,f128])).

fof(f30,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f113,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(resolution,[],[f114,f31])).

fof(f31,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl4_19
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f110,f105,f58,f113])).

fof(f58,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f105,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(resolution,[],[f106,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f98,f88,f42,f105])).

fof(f42,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f88,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f85,f78,f54,f88])).

fof(f54,plain,
    ( spl4_8
  <=> ! [X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f78,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f79,f55])).

fof(f55,plain,
    ( ! [X2,X0] :
        ( r2_hidden(X2,k1_zfmisc_1(X0))
        | ~ r1_tarski(X2,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl4_13
    | spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f72,f69,f34,f78])).

fof(f34,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f69,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(sK2,X0) )
    | spl4_3
    | ~ spl4_11 ),
    inference(resolution,[],[f70,f35])).

fof(f35,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f60,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f15,f58])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f56,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f48,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & r1_tarski(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( r1_tarski(X2,X1)
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f36,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f11,f30])).

fof(f11,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (31125)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (31131)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (31125)Refutation not found, incomplete strategy% (31125)------------------------------
% 0.21/0.48  % (31125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31125)Memory used [KB]: 10618
% 0.21/0.48  % (31125)Time elapsed: 0.056 s
% 0.21/0.48  % (31125)------------------------------
% 0.21/0.48  % (31125)------------------------------
% 0.21/0.48  % (31131)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f56,f60,f71,f80,f90,f107,f115,f130,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~spl4_4 | ~spl4_6 | spl4_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    $false | (~spl4_4 | ~spl4_6 | spl4_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl4_6 | spl4_22)),
% 0.21/0.48    inference(resolution,[],[f129,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl4_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl4_22 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~spl4_22 | ~spl4_2 | ~spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f113,f30,f128])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl4_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl4_19 <=> ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_19)),
% 0.21/0.48    inference(resolution,[],[f114,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f30])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl4_19 | ~spl4_9 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f110,f105,f58,f113])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_9 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl4_18 <=> ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_9 | ~spl4_18)),
% 0.21/0.48    inference(resolution,[],[f106,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(sK2,X0)) ) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl4_18 | ~spl4_5 | ~spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f88,f42,f105])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl4_5 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl4_15 <=> ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r1_tarski(sK2,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl4_5 | ~spl4_15)),
% 0.21/0.48    inference(resolution,[],[f89,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r1_tarski(sK2,X0)) ) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl4_15 | ~spl4_8 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f85,f78,f54,f88])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl4_8 <=> ! [X0,X2] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r2_hidden(sK2,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r1_tarski(sK2,X0)) ) | (~spl4_8 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f79,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) ) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_13 | spl4_3 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f69,f34,f78])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl4_11 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~r2_hidden(sK2,X0)) ) | (spl4_3 | ~spl4_11)),
% 0.21/0.48    inference(resolution,[],[f70,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f69])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f58])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f54])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f46])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f38])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f34])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f30])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31131)------------------------------
% 0.21/0.48  % (31131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31131)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31131)Memory used [KB]: 10618
% 0.21/0.48  % (31131)Time elapsed: 0.073 s
% 0.21/0.48  % (31131)------------------------------
% 0.21/0.48  % (31131)------------------------------
% 0.21/0.49  % (31117)Success in time 0.13 s
%------------------------------------------------------------------------------
