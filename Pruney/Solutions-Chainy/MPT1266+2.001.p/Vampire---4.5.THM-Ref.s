%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 659 expanded)
%              Number of leaves         :   26 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  433 (2557 expanded)
%              Number of equality atoms :   59 ( 677 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1336,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f1032,f1054,f1074,f1093,f1155,f1221,f1297,f1321,f1335])).

fof(f1335,plain,
    ( ~ spl2_63
    | ~ spl2_67
    | spl2_69
    | ~ spl2_75 ),
    inference(avatar_contradiction_clause,[],[f1334])).

fof(f1334,plain,
    ( $false
    | ~ spl2_63
    | ~ spl2_67
    | spl2_69
    | ~ spl2_75 ),
    inference(subsumption_resolution,[],[f1331,f1065])).

fof(f1065,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f1064,plain,
    ( spl2_67
  <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f1331,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_63
    | spl2_69
    | ~ spl2_75 ),
    inference(resolution,[],[f1168,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1168,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_63
    | spl2_69
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f1167,f125])).

fof(f125,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f73,f123])).

fof(f123,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1167,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_63
    | spl2_69
    | ~ spl2_75 ),
    inference(subsumption_resolution,[],[f1166,f62])).

fof(f1166,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_63
    | spl2_69
    | ~ spl2_75 ),
    inference(subsumption_resolution,[],[f1165,f1088])).

fof(f1088,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_69 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1086,plain,
    ( spl2_69
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f1165,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_63
    | ~ spl2_75 ),
    inference(subsumption_resolution,[],[f1158,f1024])).

fof(f1024,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1022,plain,
    ( spl2_63
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f1158,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_75 ),
    inference(resolution,[],[f1128,f230])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_struct_0(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_pre_topc(X0,X1))
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(extensionality_resolution,[],[f93,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1128,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl2_75
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f1321,plain,
    ( spl2_1
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | spl2_1
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f1298,f116])).

fof(f116,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1298,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f1233,f126])).

fof(f126,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f63,f125])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f1233,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_69 ),
    inference(resolution,[],[f1087,f251])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f249,f62])).

fof(f249,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f81,f125])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f1087,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1297,plain,
    ( spl2_2
    | ~ spl2_70 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | spl2_2
    | ~ spl2_70 ),
    inference(subsumption_resolution,[],[f1295,f120])).

fof(f120,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1295,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_70 ),
    inference(forward_demodulation,[],[f1294,f302])).

fof(f302,plain,(
    ! [X5] : k1_xboole_0 = k3_subset_1(X5,X5) ),
    inference(subsumption_resolution,[],[f297,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f297,plain,(
    ! [X5] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5))
      | k1_xboole_0 = k3_subset_1(X5,X5) ) ),
    inference(resolution,[],[f274,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f274,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f273,f124])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f72,f68])).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f273,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f87,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f85,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(f1294,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_70 ),
    inference(forward_demodulation,[],[f959,f1092])).

fof(f1092,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1090,plain,
    ( spl2_70
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f959,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f877,f129])).

fof(f129,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f94,f126])).

fof(f877,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(subsumption_resolution,[],[f873,f62])).

fof(f873,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(superposition,[],[f339,f125])).

fof(f339,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ),
    inference(resolution,[],[f76,f95])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f1221,plain,
    ( ~ spl2_1
    | spl2_69 ),
    inference(avatar_contradiction_clause,[],[f1220])).

fof(f1220,plain,
    ( $false
    | ~ spl2_1
    | spl2_69 ),
    inference(subsumption_resolution,[],[f1212,f115])).

fof(f115,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1212,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_69 ),
    inference(subsumption_resolution,[],[f1113,f126])).

fof(f1113,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_69 ),
    inference(resolution,[],[f1088,f240])).

fof(f240,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f239,f62])).

fof(f239,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f80,f125])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1155,plain,(
    spl2_75 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | spl2_75 ),
    inference(subsumption_resolution,[],[f1152,f126])).

fof(f1152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_75 ),
    inference(resolution,[],[f1151,f85])).

fof(f1151,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_75 ),
    inference(resolution,[],[f1129,f247])).

fof(f247,plain,(
    ! [X4] :
      ( r1_tarski(k2_pre_topc(sK0,X4),k2_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f213,f94])).

fof(f213,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f210,f62])).

fof(f210,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f90,f125])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1129,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | spl2_75 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1093,plain,
    ( ~ spl2_69
    | spl2_70
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f1077,f1064,f1090,f1086])).

fof(f1077,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_67 ),
    inference(resolution,[],[f1065,f349])).

fof(f349,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f224,f95])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f222,f62])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f78,f125])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1074,plain,(
    spl2_67 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | spl2_67 ),
    inference(subsumption_resolution,[],[f1072,f126])).

fof(f1072,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_67 ),
    inference(resolution,[],[f1066,f145])).

fof(f1066,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | spl2_67 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f1054,plain,(
    spl2_57 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | spl2_57 ),
    inference(subsumption_resolution,[],[f1051,f126])).

fof(f1051,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_57 ),
    inference(resolution,[],[f1049,f85])).

fof(f1049,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_57 ),
    inference(resolution,[],[f996,f213])).

fof(f996,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_57 ),
    inference(avatar_component_clause,[],[f994])).

fof(f994,plain,
    ( spl2_57
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1032,plain,
    ( ~ spl2_57
    | spl2_63
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1031,f118,f1022,f994])).

fof(f1031,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f988,f67])).

fof(f988,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f323,f968])).

fof(f968,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f959,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f323,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_subset_1(X1,X2),k1_xboole_0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f320,f124])).

fof(f320,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_subset_1(X1,X2),k1_xboole_0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f89,f302])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f122,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f64,f118,f114])).

fof(f64,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f65,f118,f114])).

fof(f65,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.56  % (25143)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.57  % (25165)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.57  % (25157)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.58  % (25149)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.58  % (25155)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.58  % (25163)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.70/0.59  % (25157)Refutation not found, incomplete strategy% (25157)------------------------------
% 1.70/0.59  % (25157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (25146)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.70/0.60  % (25157)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (25157)Memory used [KB]: 10746
% 1.70/0.60  % (25157)Time elapsed: 0.147 s
% 1.70/0.60  % (25157)------------------------------
% 1.70/0.60  % (25157)------------------------------
% 1.70/0.60  % (25154)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.70/0.60  % (25156)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.70/0.60  % (25145)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.70/0.60  % (25141)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.70/0.60  % (25153)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.70/0.61  % (25144)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.70/0.61  % (25147)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.61  % (25142)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.70/0.62  % (25148)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.70/0.62  % (25168)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.70/0.62  % (25164)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.70/0.62  % (25162)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.70/0.62  % (25152)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.70/0.63  % (25169)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.70/0.63  % (25167)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.70/0.64  % (25161)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.70/0.64  % (25159)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.70/0.64  % (25170)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.70/0.65  % (25151)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.70/0.65  % (25150)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.70/0.65  % (25151)Refutation not found, incomplete strategy% (25151)------------------------------
% 1.70/0.65  % (25151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.65  % (25151)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.65  
% 1.70/0.65  % (25151)Memory used [KB]: 10746
% 1.70/0.65  % (25151)Time elapsed: 0.219 s
% 1.70/0.65  % (25151)------------------------------
% 1.70/0.65  % (25151)------------------------------
% 1.70/0.65  % (25169)Refutation not found, incomplete strategy% (25169)------------------------------
% 1.70/0.65  % (25169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.65  % (25160)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.70/0.65  % (25169)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.65  
% 1.70/0.65  % (25169)Memory used [KB]: 10746
% 1.70/0.65  % (25169)Time elapsed: 0.217 s
% 1.70/0.65  % (25169)------------------------------
% 1.70/0.65  % (25169)------------------------------
% 1.70/0.66  % (25158)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.70/0.66  % (25166)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.59/0.72  % (25147)Refutation found. Thanks to Tanya!
% 2.59/0.72  % SZS status Theorem for theBenchmark
% 2.59/0.72  % SZS output start Proof for theBenchmark
% 2.59/0.72  fof(f1336,plain,(
% 2.59/0.72    $false),
% 2.59/0.72    inference(avatar_sat_refutation,[],[f121,f122,f1032,f1054,f1074,f1093,f1155,f1221,f1297,f1321,f1335])).
% 2.59/0.72  fof(f1335,plain,(
% 2.59/0.72    ~spl2_63 | ~spl2_67 | spl2_69 | ~spl2_75),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1334])).
% 2.59/0.72  fof(f1334,plain,(
% 2.59/0.72    $false | (~spl2_63 | ~spl2_67 | spl2_69 | ~spl2_75)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1331,f1065])).
% 2.59/0.72  fof(f1065,plain,(
% 2.59/0.72    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_67),
% 2.59/0.72    inference(avatar_component_clause,[],[f1064])).
% 2.59/0.72  fof(f1064,plain,(
% 2.59/0.72    spl2_67 <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 2.59/0.72  fof(f1331,plain,(
% 2.59/0.72    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | (~spl2_63 | spl2_69 | ~spl2_75)),
% 2.59/0.72    inference(resolution,[],[f1168,f95])).
% 2.59/0.72  fof(f95,plain,(
% 2.59/0.72    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f61])).
% 2.59/0.72  fof(f61,plain,(
% 2.59/0.72    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.72    inference(nnf_transformation,[],[f21])).
% 2.59/0.72  fof(f21,axiom,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.59/0.72  fof(f1168,plain,(
% 2.59/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_63 | spl2_69 | ~spl2_75)),
% 2.59/0.72    inference(forward_demodulation,[],[f1167,f125])).
% 2.59/0.72  fof(f125,plain,(
% 2.59/0.72    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.59/0.72    inference(resolution,[],[f73,f123])).
% 2.59/0.72  fof(f123,plain,(
% 2.59/0.72    l1_struct_0(sK0)),
% 2.59/0.72    inference(resolution,[],[f74,f62])).
% 2.59/0.72  fof(f62,plain,(
% 2.59/0.72    l1_pre_topc(sK0)),
% 2.59/0.72    inference(cnf_transformation,[],[f55])).
% 2.59/0.72  fof(f55,plain,(
% 2.59/0.72    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.59/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).
% 2.59/0.72  fof(f53,plain,(
% 2.59/0.72    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.59/0.72    introduced(choice_axiom,[])).
% 2.59/0.72  fof(f54,plain,(
% 2.59/0.72    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.59/0.72    introduced(choice_axiom,[])).
% 2.59/0.72  fof(f52,plain,(
% 2.59/0.72    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.72    inference(flattening,[],[f51])).
% 2.59/0.72  fof(f51,plain,(
% 2.59/0.72    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.72    inference(nnf_transformation,[],[f33])).
% 2.59/0.72  fof(f33,plain,(
% 2.59/0.72    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f32])).
% 2.59/0.72  fof(f32,negated_conjecture,(
% 2.59/0.72    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.59/0.72    inference(negated_conjecture,[],[f31])).
% 2.59/0.72  fof(f31,conjecture,(
% 2.59/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 2.59/0.72  fof(f74,plain,(
% 2.59/0.72    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f35])).
% 2.59/0.72  fof(f35,plain,(
% 2.59/0.72    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f25])).
% 2.59/0.72  fof(f25,axiom,(
% 2.59/0.72    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.59/0.72  fof(f73,plain,(
% 2.59/0.72    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f34])).
% 2.59/0.72  fof(f34,plain,(
% 2.59/0.72    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f23])).
% 2.59/0.72  fof(f23,axiom,(
% 2.59/0.72    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.59/0.72  fof(f1167,plain,(
% 2.59/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_63 | spl2_69 | ~spl2_75)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1166,f62])).
% 2.59/0.72  fof(f1166,plain,(
% 2.59/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_63 | spl2_69 | ~spl2_75)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1165,f1088])).
% 2.59/0.72  fof(f1088,plain,(
% 2.59/0.72    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | spl2_69),
% 2.59/0.72    inference(avatar_component_clause,[],[f1086])).
% 2.59/0.72  fof(f1086,plain,(
% 2.59/0.72    spl2_69 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 2.59/0.72  fof(f1165,plain,(
% 2.59/0.72    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_63 | ~spl2_75)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1158,f1024])).
% 2.59/0.72  fof(f1024,plain,(
% 2.59/0.72    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_63),
% 2.59/0.72    inference(avatar_component_clause,[],[f1022])).
% 2.59/0.72  fof(f1022,plain,(
% 2.59/0.72    spl2_63 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 2.59/0.72  fof(f1158,plain,(
% 2.59/0.72    ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_75),
% 2.59/0.72    inference(resolution,[],[f1128,f230])).
% 2.59/0.72  fof(f230,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X0,X1),k2_struct_0(X0)) | ~r1_tarski(k2_struct_0(X0),k2_pre_topc(X0,X1)) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(extensionality_resolution,[],[f93,f79])).
% 2.59/0.72  fof(f79,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f56])).
% 2.59/0.72  fof(f56,plain,(
% 2.59/0.72    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(nnf_transformation,[],[f40])).
% 2.59/0.72  fof(f40,plain,(
% 2.59/0.72    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f29])).
% 2.59/0.72  fof(f29,axiom,(
% 2.59/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 2.59/0.72  fof(f93,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f60])).
% 2.59/0.72  fof(f60,plain,(
% 2.59/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.72    inference(flattening,[],[f59])).
% 2.59/0.72  fof(f59,plain,(
% 2.59/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.72    inference(nnf_transformation,[],[f2])).
% 2.59/0.72  fof(f2,axiom,(
% 2.59/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.59/0.72  fof(f1128,plain,(
% 2.59/0.72    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl2_75),
% 2.59/0.72    inference(avatar_component_clause,[],[f1127])).
% 2.59/0.72  fof(f1127,plain,(
% 2.59/0.72    spl2_75 <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 2.59/0.72  fof(f1321,plain,(
% 2.59/0.72    spl2_1 | ~spl2_69),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1320])).
% 2.59/0.72  fof(f1320,plain,(
% 2.59/0.72    $false | (spl2_1 | ~spl2_69)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1298,f116])).
% 2.59/0.72  fof(f116,plain,(
% 2.59/0.72    ~v2_tops_1(sK1,sK0) | spl2_1),
% 2.59/0.72    inference(avatar_component_clause,[],[f114])).
% 2.59/0.72  fof(f114,plain,(
% 2.59/0.72    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.59/0.72  fof(f1298,plain,(
% 2.59/0.72    v2_tops_1(sK1,sK0) | ~spl2_69),
% 2.59/0.72    inference(subsumption_resolution,[],[f1233,f126])).
% 2.59/0.72  fof(f126,plain,(
% 2.59/0.72    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.59/0.72    inference(backward_demodulation,[],[f63,f125])).
% 2.59/0.72  fof(f63,plain,(
% 2.59/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.59/0.72    inference(cnf_transformation,[],[f55])).
% 2.59/0.72  fof(f1233,plain,(
% 2.59/0.72    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_69),
% 2.59/0.72    inference(resolution,[],[f1087,f251])).
% 2.59/0.72  fof(f251,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f249,f62])).
% 2.59/0.72  fof(f249,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.59/0.72    inference(superposition,[],[f81,f125])).
% 2.59/0.72  fof(f81,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f57])).
% 2.59/0.72  fof(f57,plain,(
% 2.59/0.72    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(nnf_transformation,[],[f41])).
% 2.59/0.72  fof(f41,plain,(
% 2.59/0.72    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f30])).
% 2.59/0.72  fof(f30,axiom,(
% 2.59/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 2.59/0.72  fof(f1087,plain,(
% 2.59/0.72    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_69),
% 2.59/0.72    inference(avatar_component_clause,[],[f1086])).
% 2.59/0.72  fof(f1297,plain,(
% 2.59/0.72    spl2_2 | ~spl2_70),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1296])).
% 2.59/0.72  fof(f1296,plain,(
% 2.59/0.72    $false | (spl2_2 | ~spl2_70)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1295,f120])).
% 2.59/0.72  fof(f120,plain,(
% 2.59/0.72    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 2.59/0.72    inference(avatar_component_clause,[],[f118])).
% 2.59/0.72  fof(f118,plain,(
% 2.59/0.72    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.59/0.72  fof(f1295,plain,(
% 2.59/0.72    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_70),
% 2.59/0.72    inference(forward_demodulation,[],[f1294,f302])).
% 2.59/0.72  fof(f302,plain,(
% 2.59/0.72    ( ! [X5] : (k1_xboole_0 = k3_subset_1(X5,X5)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f297,f69])).
% 2.59/0.72  fof(f69,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f19])).
% 2.59/0.72  fof(f19,axiom,(
% 2.59/0.72    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.59/0.72  fof(f297,plain,(
% 2.59/0.72    ( ! [X5] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) | k1_xboole_0 = k3_subset_1(X5,X5)) )),
% 2.59/0.72    inference(resolution,[],[f274,f131])).
% 2.59/0.72  fof(f131,plain,(
% 2.59/0.72    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.59/0.72    inference(resolution,[],[f93,f67])).
% 2.59/0.72  fof(f67,plain,(
% 2.59/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f5])).
% 2.59/0.72  fof(f5,axiom,(
% 2.59/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.59/0.72  fof(f274,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f273,f124])).
% 2.59/0.72  fof(f124,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(forward_demodulation,[],[f72,f68])).
% 2.59/0.72  fof(f68,plain,(
% 2.59/0.72    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.59/0.72    inference(cnf_transformation,[],[f13])).
% 2.59/0.72  fof(f13,axiom,(
% 2.59/0.72    ! [X0] : k2_subset_1(X0) = X0),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.59/0.72  fof(f72,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f15])).
% 2.59/0.72  fof(f15,axiom,(
% 2.59/0.72    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.59/0.72  fof(f273,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(duplicate_literal_removal,[],[f269])).
% 2.59/0.72  fof(f269,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(resolution,[],[f87,f145])).
% 2.59/0.72  fof(f145,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.72    inference(resolution,[],[f85,f94])).
% 2.59/0.72  fof(f94,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f61])).
% 2.59/0.72  fof(f85,plain,(
% 2.59/0.72    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f42])).
% 2.59/0.72  fof(f42,plain,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f16])).
% 2.59/0.72  fof(f16,axiom,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.59/0.72  fof(f87,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X2) | r1_tarski(k3_subset_1(X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f45])).
% 2.59/0.72  fof(f45,plain,(
% 2.59/0.72    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(flattening,[],[f44])).
% 2.59/0.72  fof(f44,plain,(
% 2.59/0.72    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f18])).
% 2.59/0.72  fof(f18,axiom,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).
% 2.59/0.72  fof(f1294,plain,(
% 2.59/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_70),
% 2.59/0.72    inference(forward_demodulation,[],[f959,f1092])).
% 2.59/0.72  fof(f1092,plain,(
% 2.59/0.72    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_70),
% 2.59/0.72    inference(avatar_component_clause,[],[f1090])).
% 2.59/0.72  fof(f1090,plain,(
% 2.59/0.72    spl2_70 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 2.59/0.72  fof(f959,plain,(
% 2.59/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.59/0.72    inference(resolution,[],[f877,f129])).
% 2.59/0.72  fof(f129,plain,(
% 2.59/0.72    r1_tarski(sK1,k2_struct_0(sK0))),
% 2.59/0.72    inference(resolution,[],[f94,f126])).
% 2.59/0.72  fof(f877,plain,(
% 2.59/0.72    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f873,f62])).
% 2.59/0.72  fof(f873,plain,(
% 2.59/0.72    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 2.59/0.72    inference(superposition,[],[f339,f125])).
% 2.59/0.72  fof(f339,plain,(
% 2.59/0.72    ( ! [X2,X1] : (~r1_tarski(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))) )),
% 2.59/0.72    inference(resolution,[],[f76,f95])).
% 2.59/0.72  fof(f76,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f37])).
% 2.59/0.72  fof(f37,plain,(
% 2.59/0.72    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f28])).
% 2.59/0.72  fof(f28,axiom,(
% 2.59/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.59/0.72  fof(f1221,plain,(
% 2.59/0.72    ~spl2_1 | spl2_69),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1220])).
% 2.59/0.72  fof(f1220,plain,(
% 2.59/0.72    $false | (~spl2_1 | spl2_69)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1212,f115])).
% 2.59/0.72  fof(f115,plain,(
% 2.59/0.72    v2_tops_1(sK1,sK0) | ~spl2_1),
% 2.59/0.72    inference(avatar_component_clause,[],[f114])).
% 2.59/0.72  fof(f1212,plain,(
% 2.59/0.72    ~v2_tops_1(sK1,sK0) | spl2_69),
% 2.59/0.72    inference(subsumption_resolution,[],[f1113,f126])).
% 2.59/0.72  fof(f1113,plain,(
% 2.59/0.72    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_69),
% 2.59/0.72    inference(resolution,[],[f1088,f240])).
% 2.59/0.72  fof(f240,plain,(
% 2.59/0.72    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f239,f62])).
% 2.59/0.72  fof(f239,plain,(
% 2.59/0.72    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.59/0.72    inference(superposition,[],[f80,f125])).
% 2.59/0.72  fof(f80,plain,(
% 2.59/0.72    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f57])).
% 2.59/0.72  fof(f1155,plain,(
% 2.59/0.72    spl2_75),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1154])).
% 2.59/0.72  fof(f1154,plain,(
% 2.59/0.72    $false | spl2_75),
% 2.59/0.72    inference(subsumption_resolution,[],[f1152,f126])).
% 2.59/0.72  fof(f1152,plain,(
% 2.59/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_75),
% 2.59/0.72    inference(resolution,[],[f1151,f85])).
% 2.59/0.72  fof(f1151,plain,(
% 2.59/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_75),
% 2.59/0.72    inference(resolution,[],[f1129,f247])).
% 2.59/0.72  fof(f247,plain,(
% 2.59/0.72    ( ! [X4] : (r1_tarski(k2_pre_topc(sK0,X4),k2_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.59/0.72    inference(resolution,[],[f213,f94])).
% 2.59/0.72  fof(f213,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f210,f62])).
% 2.59/0.72  fof(f210,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.59/0.72    inference(superposition,[],[f90,f125])).
% 2.59/0.72  fof(f90,plain,(
% 2.59/0.72    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f48])).
% 2.59/0.72  fof(f48,plain,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.59/0.72    inference(flattening,[],[f47])).
% 2.59/0.72  fof(f47,plain,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f24])).
% 2.59/0.72  fof(f24,axiom,(
% 2.59/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.59/0.72  fof(f1129,plain,(
% 2.59/0.72    ~r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | spl2_75),
% 2.59/0.72    inference(avatar_component_clause,[],[f1127])).
% 2.59/0.72  fof(f1093,plain,(
% 2.59/0.72    ~spl2_69 | spl2_70 | ~spl2_67),
% 2.59/0.72    inference(avatar_split_clause,[],[f1077,f1064,f1090,f1086])).
% 2.59/0.72  fof(f1077,plain,(
% 2.59/0.72    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_67),
% 2.59/0.72    inference(resolution,[],[f1065,f349])).
% 2.59/0.72  fof(f349,plain,(
% 2.59/0.72    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 2.59/0.72    inference(resolution,[],[f224,f95])).
% 2.59/0.72  fof(f224,plain,(
% 2.59/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f222,f62])).
% 2.59/0.72  fof(f222,plain,(
% 2.59/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~l1_pre_topc(sK0)) )),
% 2.59/0.72    inference(superposition,[],[f78,f125])).
% 2.59/0.72  fof(f78,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f56])).
% 2.59/0.72  fof(f1074,plain,(
% 2.59/0.72    spl2_67),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1073])).
% 2.59/0.72  fof(f1073,plain,(
% 2.59/0.72    $false | spl2_67),
% 2.59/0.72    inference(subsumption_resolution,[],[f1072,f126])).
% 2.59/0.72  fof(f1072,plain,(
% 2.59/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_67),
% 2.59/0.72    inference(resolution,[],[f1066,f145])).
% 2.59/0.72  fof(f1066,plain,(
% 2.59/0.72    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | spl2_67),
% 2.59/0.72    inference(avatar_component_clause,[],[f1064])).
% 2.59/0.72  fof(f1054,plain,(
% 2.59/0.72    spl2_57),
% 2.59/0.72    inference(avatar_contradiction_clause,[],[f1053])).
% 2.59/0.72  fof(f1053,plain,(
% 2.59/0.72    $false | spl2_57),
% 2.59/0.72    inference(subsumption_resolution,[],[f1051,f126])).
% 2.59/0.72  fof(f1051,plain,(
% 2.59/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_57),
% 2.59/0.72    inference(resolution,[],[f1049,f85])).
% 2.59/0.72  fof(f1049,plain,(
% 2.59/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_57),
% 2.59/0.72    inference(resolution,[],[f996,f213])).
% 2.59/0.72  fof(f996,plain,(
% 2.59/0.72    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_57),
% 2.59/0.72    inference(avatar_component_clause,[],[f994])).
% 2.59/0.72  fof(f994,plain,(
% 2.59/0.72    spl2_57 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.59/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 2.59/0.72  fof(f1032,plain,(
% 2.59/0.72    ~spl2_57 | spl2_63 | ~spl2_2),
% 2.59/0.72    inference(avatar_split_clause,[],[f1031,f118,f1022,f994])).
% 2.59/0.72  fof(f1031,plain,(
% 2.59/0.72    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_2),
% 2.59/0.72    inference(subsumption_resolution,[],[f988,f67])).
% 2.59/0.72  fof(f988,plain,(
% 2.59/0.72    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_2),
% 2.59/0.72    inference(superposition,[],[f323,f968])).
% 2.59/0.72  fof(f968,plain,(
% 2.59/0.72    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 2.59/0.72    inference(forward_demodulation,[],[f959,f119])).
% 2.59/0.72  fof(f119,plain,(
% 2.59/0.72    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 2.59/0.72    inference(avatar_component_clause,[],[f118])).
% 2.59/0.72  fof(f323,plain,(
% 2.59/0.72    ( ! [X2,X1] : (~r1_tarski(k3_subset_1(X1,X2),k1_xboole_0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f320,f124])).
% 2.59/0.72  fof(f320,plain,(
% 2.59/0.72    ( ! [X2,X1] : (~r1_tarski(k3_subset_1(X1,X2),k1_xboole_0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.59/0.72    inference(superposition,[],[f89,f302])).
% 2.59/0.72  fof(f89,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f58])).
% 2.59/0.72  fof(f58,plain,(
% 2.59/0.72    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(nnf_transformation,[],[f46])).
% 2.59/0.72  fof(f46,plain,(
% 2.59/0.72    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f17])).
% 2.59/0.72  fof(f17,axiom,(
% 2.59/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 2.59/0.72  fof(f122,plain,(
% 2.59/0.72    spl2_1 | spl2_2),
% 2.59/0.72    inference(avatar_split_clause,[],[f64,f118,f114])).
% 2.59/0.72  fof(f64,plain,(
% 2.59/0.72    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 2.59/0.72    inference(cnf_transformation,[],[f55])).
% 2.59/0.72  fof(f121,plain,(
% 2.59/0.72    ~spl2_1 | ~spl2_2),
% 2.59/0.72    inference(avatar_split_clause,[],[f65,f118,f114])).
% 2.59/0.72  fof(f65,plain,(
% 2.59/0.72    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.59/0.72    inference(cnf_transformation,[],[f55])).
% 2.59/0.72  % SZS output end Proof for theBenchmark
% 2.59/0.72  % (25147)------------------------------
% 2.59/0.72  % (25147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.72  % (25147)Termination reason: Refutation
% 2.59/0.72  
% 2.59/0.72  % (25147)Memory used [KB]: 11385
% 2.59/0.72  % (25147)Time elapsed: 0.279 s
% 2.59/0.72  % (25147)------------------------------
% 2.59/0.72  % (25147)------------------------------
% 2.59/0.72  % (25140)Success in time 0.354 s
%------------------------------------------------------------------------------
