%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 301 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f56,f118,f126,f162])).

fof(f162,plain,
    ( spl3_11
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f158,f117])).

fof(f117,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_11
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f158,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f29,f125])).

fof(f125,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_12
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f126,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f120,f42,f37,f123])).

fof(f37,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f120,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f93,f86])).

fof(f86,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f93,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f77,f87])).

fof(f87,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f30])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f77,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f118,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f92,f53,f42,f32,f115])).

fof(f32,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,
    ( spl3_4
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(backward_demodulation,[],[f67,f87])).

fof(f67,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(backward_demodulation,[],[f57,f65])).

fof(f65,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f34,f44,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f57,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2)))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f55,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (25358)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.44  % (25363)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (25363)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f35,f40,f45,f56,f118,f126,f162])).
% 0.22/0.44  fof(f162,plain,(
% 0.22/0.44    spl3_11 | ~spl3_12),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    $false | (spl3_11 | ~spl3_12)),
% 0.22/0.44    inference(subsumption_resolution,[],[f158,f117])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f115])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    spl3_11 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~spl3_12),
% 0.22/0.44    inference(superposition,[],[f29,f125])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f123])).
% 0.22/0.44  fof(f123,plain,(
% 0.22/0.44    spl3_12 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f23,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    spl3_12 | ~spl3_2 | ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f120,f42,f37,f123])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl3_2 | ~spl3_3)),
% 0.22/0.44    inference(superposition,[],[f93,f86])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_2),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f39,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f27,f24])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f37])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.22/0.44    inference(backward_demodulation,[],[f77,f87])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f44,f30])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)) ) | ~spl3_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f44,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    ~spl3_11 | ~spl3_1 | ~spl3_3 | spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f92,f53,f42,f32,f115])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl3_1 <=> l1_pre_topc(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_4 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | (~spl3_1 | ~spl3_3 | spl3_4)),
% 0.22/0.44    inference(backward_demodulation,[],[f67,f87])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | (~spl3_1 | ~spl3_3 | spl3_4)),
% 0.22/0.44    inference(backward_demodulation,[],[f57,f65])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_3)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f34,f44,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    l1_pre_topc(sK0) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(k1_pre_topc(sK0,sK2))) | spl3_4),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f55,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f53])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14,f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f37])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f32])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (25363)------------------------------
% 0.22/0.44  % (25363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (25363)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (25363)Memory used [KB]: 10746
% 0.22/0.44  % (25363)Time elapsed: 0.032 s
% 0.22/0.44  % (25363)------------------------------
% 0.22/0.44  % (25363)------------------------------
% 0.22/0.45  % (25347)Success in time 0.085 s
%------------------------------------------------------------------------------
