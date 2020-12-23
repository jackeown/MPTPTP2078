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
% DateTime   : Thu Dec  3 13:20:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  240 ( 426 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f93,f100,f105,f110,f114,f235,f304])).

fof(f304,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9 ),
    inference(subsumption_resolution,[],[f113,f300])).

fof(f300,plain,
    ( ! [X0] : v2_tex_2(k3_xboole_0(X0,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f245,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f245,plain,
    ( ! [X0] : v2_tex_2(k3_xboole_0(sK2,X0),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f243,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f243,plain,
    ( ! [X0] : v2_tex_2(k4_xboole_0(sK2,X0),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f237,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK2,X0),sK2)
        | v2_tex_2(k4_xboole_0(sK2,X0),sK0) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f236,f127])).

fof(f127,plain,
    ( ! [X3] : m1_subset_1(k4_xboole_0(sK2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(resolution,[],[f115,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f115,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f92,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_4
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f80,f96])).

fof(f96,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_5
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2)
        | ~ v2_tex_2(sK2,sK0)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f72,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2)
        | ~ v2_tex_2(sK2,sK0)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_9
  <=> v2_tex_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f235,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f113,f233])).

fof(f233,plain,
    ( ! [X0] : v2_tex_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f231,f52])).

fof(f231,plain,
    ( ! [X1] : v2_tex_2(k4_xboole_0(sK1,X1),sK0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f226,f57])).

fof(f226,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(sK1,X1),sK1)
        | v2_tex_2(k4_xboole_0(sK1,X1),sK0) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f101,f135])).

fof(f135,plain,
    ( ! [X3] : m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(resolution,[],[f118,f45])).

fof(f118,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f109,f56])).

fof(f109,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f89,f99])).

fof(f99,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ v2_tex_2(sK1,sK0)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f81,f62])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ v2_tex_2(sK1,sK0)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( ~ spl3_9
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f106,f103,f65,f112])).

fof(f103,plain,
    ( spl3_7
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2
    | spl3_7 ),
    inference(forward_demodulation,[],[f104,f73])).

fof(f73,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f104,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f69,f108])).

fof(f85,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f38,f103])).

fof(f38,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f100,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f36,f98,f95])).

fof(f36,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f76,f65,f91])).

fof(f76,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f66,f46])).

fof(f71,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6040)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (6056)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6029)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (6031)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6025)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (6034)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (6048)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (6033)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (6055)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (6038)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (6047)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (6028)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (6030)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (6037)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (6027)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (6026)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (6035)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (6050)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (6055)Refutation not found, incomplete strategy% (6055)------------------------------
% 0.21/0.54  % (6055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6055)Memory used [KB]: 10746
% 0.21/0.54  % (6055)Time elapsed: 0.132 s
% 0.21/0.54  % (6055)------------------------------
% 0.21/0.54  % (6055)------------------------------
% 0.21/0.54  % (6053)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (6049)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (6043)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (6041)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (6053)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f63,f67,f71,f93,f100,f105,f110,f114,f235,f304])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | spl3_9),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | spl3_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f300])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(k3_xboole_0(X0,sK2),sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.55    inference(superposition,[],[f245,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f245,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(k3_xboole_0(sK2,X0),sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.55    inference(superposition,[],[f243,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(k4_xboole_0(sK2,X0),sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f237,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK2,X0),sK2) | v2_tex_2(k4_xboole_0(sK2,X0),sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.55    inference(resolution,[],[f236,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X3] : (m1_subset_1(k4_xboole_0(sK2,X3),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.21/0.55    inference(resolution,[],[f115,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),u1_struct_0(sK0))) ) | ~spl3_4),
% 0.21/0.55    inference(resolution,[],[f92,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl3_4 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f80,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    v2_tex_2(sK2,sK0) | ~spl3_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    spl3_5 <=> v2_tex_2(sK2,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2) | ~v2_tex_2(sK2,sK0) | v2_tex_2(X0,sK0)) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f72,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2) | ~v2_tex_2(sK2,sK0) | v2_tex_2(X0,sK0)) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f66,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ~v2_tex_2(k3_xboole_0(sK1,sK2),sK0) | spl3_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    spl3_9 <=> v2_tex_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    ~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_8 | spl3_9),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.55  fof(f234,plain,(
% 0.21/0.55    $false | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_8 | spl3_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f233])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(k3_xboole_0(sK1,X0),sK0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_8)),
% 0.21/0.55    inference(superposition,[],[f231,f52])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ( ! [X1] : (v2_tex_2(k4_xboole_0(sK1,X1),sK0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f226,f57])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ( ! [X1] : (~r1_tarski(k4_xboole_0(sK1,X1),sK1) | v2_tex_2(k4_xboole_0(sK1,X1),sK0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_8)),
% 0.21/0.55    inference(resolution,[],[f101,f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X3] : (m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_8),
% 0.21/0.55    inference(resolution,[],[f118,f45])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | ~spl3_8),
% 0.21/0.55    inference(resolution,[],[f109,f56])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    spl3_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f89,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    v2_tex_2(sK1,sK0) | ~spl3_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl3_6 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~v2_tex_2(sK1,sK0) | v2_tex_2(X0,sK0)) ) | (~spl3_1 | ~spl3_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f81,f62])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~v2_tex_2(sK1,sK0) | v2_tex_2(X0,sK0)) ) | ~spl3_3),
% 0.21/0.55    inference(resolution,[],[f70,f44])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ~spl3_9 | ~spl3_2 | spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f106,f103,f65,f112])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    spl3_7 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ~v2_tex_2(k3_xboole_0(sK1,sK2),sK0) | (~spl3_2 | spl3_7)),
% 0.21/0.55    inference(forward_demodulation,[],[f104,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f66,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f103])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    spl3_8 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f85,f69,f108])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.55    inference(resolution,[],[f70,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ~spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f103])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f22])).
% 0.21/0.55  fof(f22,conjecture,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    spl3_5 | spl3_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f36,f98,f95])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    v2_tex_2(sK1,sK0) | v2_tex_2(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl3_4 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f76,f65,f91])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f66,f46])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f69])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f37,f65])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f40,f61])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6053)------------------------------
% 0.21/0.55  % (6053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6053)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6053)Memory used [KB]: 6396
% 0.21/0.55  % (6053)Time elapsed: 0.143 s
% 0.21/0.55  % (6053)------------------------------
% 0.21/0.55  % (6053)------------------------------
% 0.21/0.55  % (6051)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (6044)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (6052)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (6032)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (6042)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (6054)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (6042)Refutation not found, incomplete strategy% (6042)------------------------------
% 0.21/0.56  % (6042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6042)Memory used [KB]: 10618
% 0.21/0.56  % (6042)Time elapsed: 0.150 s
% 0.21/0.56  % (6042)------------------------------
% 0.21/0.56  % (6042)------------------------------
% 0.21/0.56  % (6045)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (6035)Refutation not found, incomplete strategy% (6035)------------------------------
% 0.21/0.56  % (6035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6035)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6035)Memory used [KB]: 10746
% 0.21/0.56  % (6035)Time elapsed: 0.158 s
% 0.21/0.56  % (6035)------------------------------
% 0.21/0.56  % (6035)------------------------------
% 0.21/0.57  % (6021)Success in time 0.205 s
%------------------------------------------------------------------------------
