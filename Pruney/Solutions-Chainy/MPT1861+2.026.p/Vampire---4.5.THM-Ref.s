%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:55 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 159 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 499 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f94,f117,f392,f393,f621,f629])).

fof(f629,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | spl3_24 ),
    inference(unit_resulting_resolution,[],[f36,f620,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f620,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl3_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f621,plain,
    ( ~ spl3_24
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f602,f276,f82,f618])).

fof(f82,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f276,plain,
    ( spl3_16
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(X1,u1_struct_0(sK0))
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f602,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_16 ),
    inference(resolution,[],[f537,f19])).

fof(f19,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f537,plain,
    ( ! [X2,X1] :
        ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK2)) )
    | ~ spl3_16 ),
    inference(duplicate_literal_removal,[],[f530])).

fof(f530,plain,
    ( ! [X2,X1] :
        ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_16 ),
    inference(resolution,[],[f415,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_subset_1(X2,X0,X1),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f80,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f72,f35])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f415,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,X2),sK2)
        | v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_16 ),
    inference(resolution,[],[f277,f72])).

fof(f277,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X1,sK2)
        | v2_tex_2(X1,sK0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f276])).

fof(f393,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_16 ),
    inference(avatar_split_clause,[],[f359,f276,f39,f109])).

fof(f109,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f39,plain,
    ( spl3_1
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f359,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v2_tex_2(sK2,sK0)
      | v2_tex_2(X0,sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f268,f47])).

fof(f47,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f268,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X8,u1_struct_0(X6))
      | ~ r1_tarski(X7,X8)
      | ~ v2_tex_2(X8,X6)
      | v2_tex_2(X7,X6)
      | ~ r1_tarski(X7,u1_struct_0(X6))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f106,f29])).

fof(f106,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(X4,X2)
      | ~ v2_tex_2(X2,X3)
      | v2_tex_2(X4,X3)
      | ~ r1_tarski(X4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f22,f29])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f392,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f21,f45,f18,f20,f19,f313])).

fof(f313,plain,(
    ! [X6,X8,X7] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v2_tex_2(X7,X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v2_tex_2(X7,X6)
      | v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f107,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X2,X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f107,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k9_subset_1(u1_struct_0(X6),X7,X8),X5)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v2_tex_2(X5,X6)
      | v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f22,f31])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f21,f111])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f94,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f18,f84])).

fof(f84,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f46,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f17,f43,f39])).

fof(f17,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (30708)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (30724)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (30716)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.56  % (30705)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.57  % (30719)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.58  % (30716)Refutation found. Thanks to Tanya!
% 1.56/0.58  % SZS status Theorem for theBenchmark
% 1.56/0.58  % (30721)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.58  % (30727)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.58  % (30711)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.58  % SZS output start Proof for theBenchmark
% 1.56/0.58  fof(f630,plain,(
% 1.56/0.58    $false),
% 1.56/0.58    inference(avatar_sat_refutation,[],[f46,f94,f117,f392,f393,f621,f629])).
% 1.56/0.58  fof(f629,plain,(
% 1.56/0.58    spl3_24),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f627])).
% 1.56/0.58  fof(f627,plain,(
% 1.56/0.58    $false | spl3_24),
% 1.56/0.58    inference(unit_resulting_resolution,[],[f36,f620,f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f7])).
% 1.56/0.58  fof(f7,axiom,(
% 1.56/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.58  fof(f620,plain,(
% 1.56/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl3_24),
% 1.56/0.58    inference(avatar_component_clause,[],[f618])).
% 1.56/0.58  fof(f618,plain,(
% 1.56/0.58    spl3_24 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.56/0.58  fof(f36,plain,(
% 1.56/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.58    inference(cnf_transformation,[],[f1])).
% 1.56/0.58  fof(f1,axiom,(
% 1.56/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.58  fof(f621,plain,(
% 1.56/0.58    ~spl3_24 | ~spl3_7 | ~spl3_16),
% 1.56/0.58    inference(avatar_split_clause,[],[f602,f276,f82,f618])).
% 1.56/0.58  fof(f82,plain,(
% 1.56/0.58    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.56/0.58  fof(f276,plain,(
% 1.56/0.58    spl3_16 <=> ! [X1] : (~r1_tarski(X1,sK2) | ~r1_tarski(X1,u1_struct_0(sK0)) | v2_tex_2(X1,sK0))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.56/0.58  fof(f602,plain,(
% 1.56/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl3_16),
% 1.56/0.58    inference(resolution,[],[f537,f19])).
% 1.56/0.58  fof(f19,plain,(
% 1.56/0.58    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f12,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f11])).
% 1.56/0.58  fof(f11,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f10])).
% 1.56/0.58  fof(f10,negated_conjecture,(
% 1.56/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.56/0.58    inference(negated_conjecture,[],[f9])).
% 1.56/0.58  fof(f9,conjecture,(
% 1.56/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 1.56/0.58  fof(f537,plain,(
% 1.56/0.58    ( ! [X2,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(sK2))) ) | ~spl3_16),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f530])).
% 1.56/0.58  fof(f530,plain,(
% 1.56/0.58    ( ! [X2,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_16),
% 1.56/0.58    inference(resolution,[],[f415,f103])).
% 1.56/0.58  fof(f103,plain,(
% 1.56/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_subset_1(X2,X0,X1),X3) | ~m1_subset_1(X1,k1_zfmisc_1(X3)) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.56/0.58    inference(superposition,[],[f80,f35])).
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(definition_unfolding,[],[f32,f33])).
% 1.56/0.58  fof(f33,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.56/0.58    inference(definition_unfolding,[],[f24,f25])).
% 1.56/0.58  fof(f25,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f3])).
% 1.56/0.58  fof(f3,axiom,(
% 1.56/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.58  fof(f24,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f6])).
% 1.56/0.58  fof(f6,axiom,(
% 1.56/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.58  fof(f32,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f16])).
% 1.56/0.58  fof(f16,plain,(
% 1.56/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f5])).
% 1.56/0.58  fof(f5,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.56/0.58  fof(f80,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f76])).
% 1.56/0.58  fof(f76,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(superposition,[],[f72,f35])).
% 1.56/0.58  fof(f72,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.56/0.58    inference(resolution,[],[f31,f30])).
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f7])).
% 1.56/0.58  fof(f31,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f15])).
% 1.56/0.58  fof(f15,plain,(
% 1.56/0.58    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f4])).
% 1.56/0.58  fof(f4,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.56/0.58  fof(f415,plain,(
% 1.56/0.58    ( ! [X2,X1] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,X2),sK2) | v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_16),
% 1.56/0.58    inference(resolution,[],[f277,f72])).
% 1.56/0.58  fof(f277,plain,(
% 1.56/0.58    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X1,sK2) | v2_tex_2(X1,sK0)) ) | ~spl3_16),
% 1.56/0.58    inference(avatar_component_clause,[],[f276])).
% 1.56/0.58  fof(f393,plain,(
% 1.56/0.58    ~spl3_9 | ~spl3_1 | spl3_16),
% 1.56/0.58    inference(avatar_split_clause,[],[f359,f276,f39,f109])).
% 1.56/0.58  fof(f109,plain,(
% 1.56/0.58    spl3_9 <=> l1_pre_topc(sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.56/0.58  fof(f39,plain,(
% 1.56/0.58    spl3_1 <=> v2_tex_2(sK2,sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.56/0.58  fof(f359,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v2_tex_2(sK2,sK0) | v2_tex_2(X0,sK0) | ~r1_tarski(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f268,f47])).
% 1.56/0.58  fof(f47,plain,(
% 1.56/0.58    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.56/0.58    inference(resolution,[],[f30,f18])).
% 1.56/0.58  fof(f18,plain,(
% 1.56/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f268,plain,(
% 1.56/0.58    ( ! [X6,X8,X7] : (~r1_tarski(X8,u1_struct_0(X6)) | ~r1_tarski(X7,X8) | ~v2_tex_2(X8,X6) | v2_tex_2(X7,X6) | ~r1_tarski(X7,u1_struct_0(X6)) | ~l1_pre_topc(X6)) )),
% 1.56/0.58    inference(resolution,[],[f106,f29])).
% 1.56/0.58  fof(f106,plain,(
% 1.56/0.58    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(X4,X2) | ~v2_tex_2(X2,X3) | v2_tex_2(X4,X3) | ~r1_tarski(X4,u1_struct_0(X3))) )),
% 1.56/0.58    inference(resolution,[],[f22,f29])).
% 1.56/0.58  fof(f22,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f14])).
% 1.56/0.58  fof(f14,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f13])).
% 1.56/0.58  fof(f13,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f8])).
% 1.56/0.58  fof(f8,axiom,(
% 1.56/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 1.56/0.58  fof(f392,plain,(
% 1.56/0.58    ~spl3_2),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f378])).
% 1.56/0.58  fof(f378,plain,(
% 1.56/0.58    $false | ~spl3_2),
% 1.56/0.58    inference(unit_resulting_resolution,[],[f21,f45,f18,f20,f19,f313])).
% 1.56/0.58  fof(f313,plain,(
% 1.56/0.58    ( ! [X6,X8,X7] : (v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~v2_tex_2(X7,X6) | ~l1_pre_topc(X6) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f304])).
% 1.56/0.58  fof(f304,plain,(
% 1.56/0.58    ( ! [X6,X8,X7] : (~l1_pre_topc(X6) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~v2_tex_2(X7,X6) | v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.56/0.58    inference(resolution,[],[f107,f78])).
% 1.56/0.58  fof(f78,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X2,X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.56/0.58    inference(superposition,[],[f34,f35])).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f23,f33])).
% 1.56/0.58  fof(f23,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f2])).
% 1.56/0.58  fof(f2,axiom,(
% 1.56/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.56/0.58  fof(f107,plain,(
% 1.56/0.58    ( ! [X6,X8,X7,X5] : (~r1_tarski(k9_subset_1(u1_struct_0(X6),X7,X8),X5) | ~l1_pre_topc(X6) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6))) | ~v2_tex_2(X5,X6) | v2_tex_2(k9_subset_1(u1_struct_0(X6),X7,X8),X6) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.56/0.58    inference(resolution,[],[f22,f31])).
% 1.56/0.58  fof(f20,plain,(
% 1.56/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    v2_tex_2(sK1,sK0) | ~spl3_2),
% 1.56/0.58    inference(avatar_component_clause,[],[f43])).
% 1.56/0.58  fof(f43,plain,(
% 1.56/0.58    spl3_2 <=> v2_tex_2(sK1,sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.56/0.58  fof(f21,plain,(
% 1.56/0.58    l1_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f117,plain,(
% 1.56/0.58    spl3_9),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f116])).
% 1.56/0.58  fof(f116,plain,(
% 1.56/0.58    $false | spl3_9),
% 1.56/0.58    inference(subsumption_resolution,[],[f21,f111])).
% 1.56/0.58  fof(f111,plain,(
% 1.56/0.58    ~l1_pre_topc(sK0) | spl3_9),
% 1.56/0.58    inference(avatar_component_clause,[],[f109])).
% 1.56/0.58  fof(f94,plain,(
% 1.56/0.58    spl3_7),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f90])).
% 1.56/0.58  fof(f90,plain,(
% 1.56/0.58    $false | spl3_7),
% 1.56/0.58    inference(subsumption_resolution,[],[f18,f84])).
% 1.56/0.58  fof(f84,plain,(
% 1.56/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 1.56/0.58    inference(avatar_component_clause,[],[f82])).
% 1.56/0.58  fof(f46,plain,(
% 1.56/0.58    spl3_1 | spl3_2),
% 1.56/0.58    inference(avatar_split_clause,[],[f17,f43,f39])).
% 1.56/0.58  fof(f17,plain,(
% 1.56/0.58    v2_tex_2(sK1,sK0) | v2_tex_2(sK2,sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  % SZS output end Proof for theBenchmark
% 1.56/0.58  % (30716)------------------------------
% 1.56/0.58  % (30716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (30716)Termination reason: Refutation
% 1.56/0.58  
% 1.56/0.58  % (30716)Memory used [KB]: 6524
% 1.56/0.58  % (30716)Time elapsed: 0.158 s
% 1.56/0.58  % (30716)------------------------------
% 1.56/0.58  % (30716)------------------------------
% 1.56/0.59  % (30697)Success in time 0.221 s
%------------------------------------------------------------------------------
