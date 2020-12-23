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
% DateTime   : Thu Dec  3 13:11:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 115 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  214 ( 312 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f45,f49,f53,f57,f65,f69,f84,f89,f95,f101,f112,f118,f121])).

fof(f121,plain,
    ( spl2_1
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl2_1
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f119,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_14
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f119,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl2_1
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f35,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_18
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f35,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f118,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f113,f110,f38,f115])).

fof(f38,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f110,plain,
    ( spl2_17
  <=> ! [X2] :
        ( k1_xboole_0 = k1_struct_0(X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f113,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(resolution,[],[f111,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f111,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(X2)
        | k1_xboole_0 = k1_struct_0(X2) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f108,f99,f67,f43,f110])).

fof(f43,plain,
    ( spl2_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f99,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f108,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_struct_0(X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f44,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f103,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_struct_0(X2)
        | ~ l1_pre_topc(X2)
        | ~ r1_tarski(k1_xboole_0,sK1(X2,k1_xboole_0)) )
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f100,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f97,f55,f47,f99])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X1)
        | k1_struct_0(X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f97,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_struct_0(X0) = X1
        | r2_hidden(sK1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f95,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f90,f87,f38,f92])).

fof(f87,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f90,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f88,f40])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl2_13
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f85,f82,f63,f87])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X0] :
        ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) )
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f80,f51,f47,f82])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f80,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_struct_0(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.40  % (20444)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (20447)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (20448)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.43  % (20445)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (20448)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f36,f41,f45,f49,f53,f57,f65,f69,f84,f89,f95,f101,f112,f118,f121])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    spl2_1 | ~spl2_14 | ~spl2_18),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_14 | ~spl2_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f119,f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl2_14 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl2_1 | ~spl2_18)),
% 0.21/0.43    inference(backward_demodulation,[],[f35,f117])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    k1_xboole_0 = k1_struct_0(sK0) | ~spl2_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f115])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl2_18 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl2_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    spl2_18 | ~spl2_2 | ~spl2_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f110,f38,f115])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    spl2_17 <=> ! [X2] : (k1_xboole_0 = k1_struct_0(X2) | ~l1_pre_topc(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    k1_xboole_0 = k1_struct_0(sK0) | (~spl2_2 | ~spl2_17)),
% 0.21/0.43    inference(resolution,[],[f111,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ( ! [X2] : (~l1_pre_topc(X2) | k1_xboole_0 = k1_struct_0(X2)) ) | ~spl2_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f110])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    spl2_17 | ~spl2_3 | ~spl2_9 | ~spl2_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f108,f99,f67,f43,f110])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl2_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl2_9 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl2_15 <=> ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k1_struct_0(X2) | ~l1_pre_topc(X2)) ) | (~spl2_3 | ~spl2_9 | ~spl2_15)),
% 0.21/0.43    inference(subsumption_resolution,[],[f103,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k1_struct_0(X2) | ~l1_pre_topc(X2) | ~r1_tarski(k1_xboole_0,sK1(X2,k1_xboole_0))) ) | (~spl2_9 | ~spl2_15)),
% 0.21/0.43    inference(resolution,[],[f100,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl2_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl2_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f99])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl2_15 | ~spl2_4 | ~spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f97,f55,f47,f99])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_4 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl2_6 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.43    inference(resolution,[],[f56,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_struct_0(X0) = X1 | r2_hidden(sK1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f90,f87,f38,f92])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl2_13 <=> ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl2_2 | ~spl2_13)),
% 0.21/0.43    inference(resolution,[],[f88,f40])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0)) ) | ~spl2_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl2_13 | ~spl2_8 | ~spl2_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f82,f63,f87])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl2_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl2_12 <=> ! [X0] : (r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0)) ) | (~spl2_8 | ~spl2_12)),
% 0.21/0.43    inference(resolution,[],[f83,f64])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0)) ) | ~spl2_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl2_12 | ~spl2_4 | ~spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f80,f51,f47,f82])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.43    inference(resolution,[],[f52,f48])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f47])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f38])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f33])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (20448)------------------------------
% 0.21/0.43  % (20448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (20448)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (20448)Memory used [KB]: 6140
% 0.21/0.43  % (20448)Time elapsed: 0.026 s
% 0.21/0.43  % (20448)------------------------------
% 0.21/0.43  % (20448)------------------------------
% 0.21/0.43  % (20437)Success in time 0.073 s
%------------------------------------------------------------------------------
