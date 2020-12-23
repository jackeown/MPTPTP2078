%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t22_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:29 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 605 expanded)
%              Number of leaves         :   57 ( 226 expanded)
%              Depth                    :   13
%              Number of atoms          :  430 (1166 expanded)
%              Number of equality atoms :   82 ( 265 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f108,f115,f124,f131,f148,f159,f167,f177,f186,f194,f218,f228,f236,f244,f280,f299,f312,f357,f411,f448,f461,f522,f573,f596,f614,f652,f862,f885,f923,f1129,f1132])).

fof(f1132,plain,
    ( ~ spl4_52
    | spl4_71 ),
    inference(avatar_contradiction_clause,[],[f1131])).

fof(f1131,plain,
    ( $false
    | ~ spl4_52
    | ~ spl4_71 ),
    inference(subsumption_resolution,[],[f1130,f460])).

fof(f460,plain,
    ( k3_xboole_0(u1_struct_0(sK0),sK1) = sK1
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_52
  <=> k3_xboole_0(u1_struct_0(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1130,plain,
    ( k3_xboole_0(u1_struct_0(sK0),sK1) != sK1
    | ~ spl4_71 ),
    inference(superposition,[],[f1128,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t48_xboole_1)).

fof(f1128,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl4_71
  <=> k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1129,plain,
    ( ~ spl4_71
    | ~ spl4_12
    | spl4_47 ),
    inference(avatar_split_clause,[],[f932,f355,f157,f1127])).

fof(f157,plain,
    ( spl4_12
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f355,plain,
    ( spl4_47
  <=> k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f932,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f929,f535])).

fof(f535,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0) = k4_xboole_0(u1_struct_0(sK0),X0)
    | ~ spl4_12 ),
    inference(resolution,[],[f89,f158])).

fof(f158,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',redefinition_k7_subset_1)).

fof(f929,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != sK1
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(superposition,[],[f356,f535])).

fof(f356,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != sK1
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f355])).

fof(f923,plain,
    ( spl4_68
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f892,f113,f921])).

fof(f921,plain,
    ( spl4_68
  <=> k3_xboole_0(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))) = sK2(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f113,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f892,plain,
    ( k3_xboole_0(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))) = sK2(k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f705,f207])).

fof(f207,plain,(
    ! [X1] : k3_xboole_0(X1,sK2(k1_zfmisc_1(X1))) = sK2(k1_zfmisc_1(X1)) ),
    inference(superposition,[],[f169,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',commutativity_k3_xboole_0)).

fof(f169,plain,(
    ! [X0] : k3_xboole_0(sK2(k1_zfmisc_1(X0)),X0) = sK2(k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f79,f140])).

fof(f140,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',existence_m1_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t3_subset)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t28_xboole_1)).

fof(f705,plain,
    ( ! [X1] : k3_xboole_0(sK1,X1) = k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,X1))
    | ~ spl4_4 ),
    inference(superposition,[],[f575,f77])).

fof(f575,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f565,f79])).

fof(f565,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK1,X2),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f559,f78])).

fof(f559,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f557,f114])).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f557,plain,
    ( ! [X0] :
        ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4 ),
    inference(superposition,[],[f314,f547])).

fof(f547,plain,
    ( ! [X27] : k7_subset_1(u1_struct_0(sK0),sK1,X27) = k4_xboole_0(sK1,X27)
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f114])).

fof(f314,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_subset_1(X4,X3,X5),X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f87,f83])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',dt_k7_subset_1)).

fof(f885,plain,
    ( spl4_66
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f597,f594,f883])).

fof(f883,plain,
    ( spl4_66
  <=> k3_xboole_0(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) = sK2(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f594,plain,
    ( spl4_58
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f597,plain,
    ( k3_xboole_0(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) = sK2(k1_zfmisc_1(sK1))
    | ~ spl4_58 ),
    inference(resolution,[],[f595,f79])).

fof(f595,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f594])).

fof(f862,plain,
    ( spl4_64
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f799,f113,f860])).

fof(f860,plain,
    ( spl4_64
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f799,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f771,f169])).

fof(f771,plain,
    ( ! [X7] : r1_tarski(k3_xboole_0(X7,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f764,f169])).

fof(f764,plain,
    ( ! [X6,X5] : r1_tarski(k3_xboole_0(X6,k3_xboole_0(X5,sK1)),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f760,f725])).

fof(f725,plain,
    ( ! [X10,X11] : k3_xboole_0(X10,k3_xboole_0(X11,sK1)) = k9_subset_1(u1_struct_0(sK0),X10,k3_xboole_0(X11,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f90,f629])).

fof(f629,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f606,f77])).

fof(f606,plain,
    ( ! [X2] : m1_subset_1(k3_xboole_0(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f560,f78])).

fof(f560,plain,
    ( ! [X1] : m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f558,f114])).

fof(f558,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4 ),
    inference(superposition,[],[f87,f547])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',redefinition_k9_subset_1)).

fof(f760,plain,
    ( ! [X6,X5] : r1_tarski(k9_subset_1(u1_struct_0(sK0),X6,k3_xboole_0(X5,sK1)),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f378,f738])).

fof(f738,plain,
    ( ! [X38] : k3_xboole_0(X38,sK1) = k9_subset_1(u1_struct_0(sK0),X38,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f90,f114])).

fof(f378,plain,
    ( ! [X4,X5] : r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,k9_subset_1(u1_struct_0(sK0),X5,sK1)),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f324,f83])).

fof(f324,plain,
    ( ! [X0,X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k9_subset_1(u1_struct_0(sK0),X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f322,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',dt_k9_subset_1)).

fof(f322,plain,
    ( ! [X7] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X7,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f88,f114])).

fof(f652,plain,
    ( spl4_62
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f632,f113,f650])).

fof(f650,plain,
    ( spl4_62
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f632,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f606,f207])).

fof(f614,plain,
    ( spl4_60
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f603,f113,f612])).

fof(f612,plain,
    ( spl4_60
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f603,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f560,f202])).

fof(f202,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f197,f71])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t2_boole)).

fof(f197,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f78,f69])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t3_boole)).

fof(f596,plain,
    ( spl4_58
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f582,f113,f594])).

fof(f582,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f565,f207])).

fof(f573,plain,
    ( spl4_56
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f562,f113,f571])).

fof(f571,plain,
    ( spl4_56
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f562,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f559,f202])).

fof(f522,plain,
    ( spl4_54
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f451,f446,f520])).

fof(f520,plain,
    ( spl4_54
  <=> k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f446,plain,
    ( spl4_50
  <=> k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f451,plain,
    ( k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f449,f202])).

fof(f449,plain,
    ( k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_50 ),
    inference(superposition,[],[f390,f447])).

fof(f447,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f446])).

fof(f390,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f198,f77])).

fof(f198,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f78,f78])).

fof(f461,plain,
    ( spl4_52
    | ~ spl4_16
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f454,f446,f175,f459])).

fof(f175,plain,
    ( spl4_16
  <=> k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f454,plain,
    ( k3_xboole_0(u1_struct_0(sK0),sK1) = sK1
    | ~ spl4_16
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f453,f176])).

fof(f176,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f453,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f452,f77])).

fof(f452,plain,
    ( k3_xboole_0(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f450,f78])).

fof(f450,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_50 ),
    inference(superposition,[],[f198,f447])).

fof(f448,plain,
    ( spl4_50
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f431,f175,f446])).

fof(f431,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_16 ),
    inference(superposition,[],[f390,f176])).

fof(f411,plain,
    ( spl4_48
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f403,f175,f409])).

fof(f409,plain,
    ( spl4_48
  <=> k3_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f403,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f395,f202])).

fof(f395,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = k4_xboole_0(sK1,sK1)
    | ~ spl4_16 ),
    inference(superposition,[],[f198,f176])).

fof(f357,plain,
    ( ~ spl4_47
    | ~ spl4_6
    | spl4_29 ),
    inference(avatar_split_clause,[],[f245,f242,f122,f355])).

fof(f122,plain,
    ( spl4_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f242,plain,
    ( spl4_29
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f245,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != sK1
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f243,f123])).

fof(f123,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f243,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != sK1
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f312,plain,
    ( ~ spl4_43
    | spl4_32
    | spl4_44
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f255,f157,f310,f272,f304])).

fof(f304,plain,
    ( spl4_43
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f272,plain,
    ( spl4_32
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f310,plain,
    ( spl4_44
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f255,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(resolution,[],[f196,f158])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f179,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t2_subset)).

fof(f179,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',antisymmetry_r2_hidden)).

fof(f299,plain,
    ( ~ spl4_37
    | spl4_38
    | spl4_40
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f257,f234,f297,f291,f285])).

fof(f285,plain,
    ( spl4_37
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f291,plain,
    ( spl4_38
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f297,plain,
    ( spl4_40
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f234,plain,
    ( spl4_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f257,plain,
    ( v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_26 ),
    inference(resolution,[],[f196,f235])).

fof(f235,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f234])).

fof(f280,plain,
    ( ~ spl4_31
    | spl4_32
    | spl4_34
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f258,f113,f278,f272,f266])).

fof(f266,plain,
    ( spl4_31
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f278,plain,
    ( spl4_34
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f258,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f196,f114])).

fof(f244,plain,(
    ~ spl4_29 ),
    inference(avatar_split_clause,[],[f68,f242])).

fof(f68,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) != sK1
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',t22_pre_topc)).

fof(f236,plain,
    ( spl4_26
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f221,f216,f234])).

fof(f216,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f221,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f75,f217])).

fof(f217,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f228,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f220,f216,f226])).

fof(f226,plain,
    ( spl4_24
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f220,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(superposition,[],[f140,f217])).

fof(f218,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f206,f216])).

fof(f206,plain,(
    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f169,f71])).

fof(f194,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f187,f184,f192])).

fof(f192,plain,
    ( spl4_20
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f184,plain,
    ( spl4_18
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f187,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ spl4_18 ),
    inference(resolution,[],[f185,f83])).

fof(f185,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f152,f129,f106,f184])).

fof(f106,plain,
    ( spl4_2
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f129,plain,
    ( spl4_8
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f152,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f150,f130])).

fof(f130,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f150,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2 ),
    inference(resolution,[],[f74,f107])).

fof(f107,plain,
    ( l1_struct_0(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',dt_k2_struct_0)).

fof(f177,plain,
    ( spl4_16
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f168,f146,f175])).

fof(f146,plain,
    ( spl4_10
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f168,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1
    | ~ spl4_10 ),
    inference(resolution,[],[f79,f147])).

fof(f147,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f160,f157,f165])).

fof(f165,plain,
    ( spl4_14
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f160,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(resolution,[],[f158,f83])).

fof(f159,plain,
    ( spl4_12
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f151,f122,f99,f157])).

fof(f99,plain,
    ( spl4_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f151,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f149,f123])).

fof(f149,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f74,f100])).

fof(f100,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f148,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f141,f113,f146])).

fof(f141,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f83,f114])).

fof(f131,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f117,f106,f129])).

fof(f117,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f107])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',d3_struct_0)).

fof(f124,plain,
    ( spl4_6
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f116,f99,f122])).

fof(f116,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f73,f100])).

fof(f115,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f67,f113])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f108,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f94,f106])).

fof(f94,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f64])).

fof(f64,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t22_pre_topc.p',existence_l1_struct_0)).

fof(f101,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f66,f99])).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
