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
% DateTime   : Thu Dec  3 13:13:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 105 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  164 ( 253 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f55,f70,f86,f123,f171,f182,f226,f470])).

fof(f470,plain,
    ( ~ spl3_2
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f468,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f468,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_2
    | ~ spl3_35 ),
    inference(resolution,[],[f225,f35])).

fof(f35,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f226,plain,
    ( spl3_35
    | ~ spl3_1
    | spl3_28 ),
    inference(avatar_split_clause,[],[f222,f179,f28,f224])).

fof(f28,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f179,plain,
    ( spl3_28
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_1
    | spl3_28 ),
    inference(subsumption_resolution,[],[f220,f30])).

fof(f30,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(sK0) )
    | spl3_28 ),
    inference(resolution,[],[f181,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f181,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,
    ( ~ spl3_28
    | spl3_26 ),
    inference(avatar_split_clause,[],[f173,f168,f179])).

fof(f168,plain,
    ( spl3_26
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f173,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_26 ),
    inference(resolution,[],[f170,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f170,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f168])).

fof(f171,plain,
    ( ~ spl3_26
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f165,f121,f43,f168])).

fof(f43,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( spl3_18
  <=> ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3)))
        | ~ r1_tarski(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f165,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(resolution,[],[f122,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f122,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3)))
        | ~ r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl3_18
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f115,f84,f121])).

fof(f84,plain,
    ( spl3_11
  <=> ! [X2] :
        ( ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f115,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3)))
        | ~ r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl3_11 ),
    inference(resolution,[],[f85,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f85,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f78,f68,f84])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f78,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f25])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f58,f53,f68])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl3_5 ),
    inference(superposition,[],[f54,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,
    ( spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f51,f38,f53])).

fof(f38,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f43])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(f41,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:55:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (1452)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (1452)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f471,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f55,f70,f86,f123,f171,f182,f226,f470])).
% 0.21/0.44  fof(f470,plain,(
% 0.21/0.44    ~spl3_2 | ~spl3_35),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f469])).
% 0.21/0.44  fof(f469,plain,(
% 0.21/0.44    $false | (~spl3_2 | ~spl3_35)),
% 0.21/0.44    inference(subsumption_resolution,[],[f468,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f20,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.44  fof(f468,plain,(
% 0.21/0.44    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl3_2 | ~spl3_35)),
% 0.21/0.44    inference(resolution,[],[f225,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl3_2 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_35),
% 0.21/0.44    inference(avatar_component_clause,[],[f224])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    spl3_35 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.44  fof(f226,plain,(
% 0.21/0.44    spl3_35 | ~spl3_1 | spl3_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f222,f179,f28,f224])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    spl3_28 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl3_1 | spl3_28)),
% 0.21/0.44    inference(subsumption_resolution,[],[f220,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f28])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(sK0)) ) | spl3_28),
% 0.21/0.44    inference(resolution,[],[f181,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f179])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ~spl3_28 | spl3_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f173,f168,f179])).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    spl3_26 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_26),
% 0.21/0.44    inference(resolution,[],[f170,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | spl3_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f168])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ~spl3_26 | ~spl3_4 | ~spl3_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f165,f121,f43,f168])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl3_18 <=> ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~r1_tarski(X3,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl3_4 | ~spl3_18)),
% 0.21/0.44    inference(resolution,[],[f122,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f43])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~r1_tarski(X3,u1_struct_0(sK0))) ) | ~spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl3_18 | ~spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f115,f84,f121])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl3_11 <=> ! [X2] : (~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~r1_tarski(X3,u1_struct_0(sK0))) ) | ~spl3_11),
% 0.21/0.44    inference(resolution,[],[f85,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ( ! [X2] : (~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(X2))) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl3_11 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f78,f68,f84])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl3_8 <=> ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X2] : (~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(X2))) ) | ~spl3_8),
% 0.21/0.44    inference(resolution,[],[f69,f25])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl3_8 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f58,f53,f68])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl3_5 <=> ! [X0] : ~r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0)) ) | ~spl3_5),
% 0.21/0.44    inference(superposition,[],[f54,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl3_5 | spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f51,f38,f53])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl3_3),
% 0.21/0.44    inference(resolution,[],[f50,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(resolution,[],[f26,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f43])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f28])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (1452)------------------------------
% 0.21/0.44  % (1452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (1452)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (1452)Memory used [KB]: 10746
% 0.21/0.44  % (1452)Time elapsed: 0.015 s
% 0.21/0.44  % (1452)------------------------------
% 0.21/0.44  % (1452)------------------------------
% 0.21/0.44  % (1454)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (1451)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (1450)Success in time 0.083 s
%------------------------------------------------------------------------------
