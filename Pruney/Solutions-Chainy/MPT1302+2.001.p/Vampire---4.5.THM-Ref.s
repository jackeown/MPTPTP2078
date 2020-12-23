%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 368 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  291 (1383 expanded)
%              Number of equality atoms :   42 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f1390,f1427,f1485,f1576,f1580,f1584])).

fof(f1584,plain,
    ( ~ spl5_5
    | ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f1583])).

fof(f1583,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f1582,f167])).

fof(f167,plain,(
    ~ v1_tops_2(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f21,f162])).

fof(f162,plain,(
    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f158,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f21,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f1582,plain,
    ( v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f1581,f1523])).

fof(f1523,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f149,f162])).

fof(f149,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_5
  <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1581,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_23 ),
    inference(resolution,[],[f1575,f466])).

fof(f466,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK0,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f460,f18])).

fof(f460,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK3(sK0,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X1,sK0) ) ),
    inference(resolution,[],[f458,f20])).

fof(f20,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f458,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK3(sK0,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f457,f454])).

fof(f454,plain,(
    ! [X0] :
      ( v1_tops_2(X0,sK0)
      | m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f457,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK3(sK0,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f456,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK3(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f456,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f24,f23])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1575,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f1573])).

fof(f1573,plain,
    ( spl5_23
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1580,plain,
    ( ~ spl5_5
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f1579])).

fof(f1579,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1578,f167])).

fof(f1578,plain,
    ( v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1577,f1523])).

fof(f1577,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_22 ),
    inference(resolution,[],[f1571,f465])).

fof(f465,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f459,f22])).

fof(f459,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK3(sK0,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f458,f19])).

fof(f19,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f1571,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f1569])).

fof(f1569,plain,
    ( spl5_22
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1576,plain,
    ( spl5_22
    | spl5_23
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1567,f152,f1573,f1569])).

fof(f152,plain,
    ( spl5_6
  <=> r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1567,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f1522,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1522,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f154,f162])).

fof(f154,plain,
    ( r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1485,plain,
    ( spl5_5
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f1484])).

fof(f1484,plain,
    ( $false
    | spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f1446,f165])).

fof(f165,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_5 ),
    inference(backward_demodulation,[],[f156,f162])).

fof(f156,plain,
    ( ~ r1_tarski(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_5 ),
    inference(resolution,[],[f150,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f150,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1446,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(superposition,[],[f28,f1389])).

fof(f1389,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1387,plain,
    ( spl5_11
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1427,plain,
    ( spl5_5
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f1426])).

fof(f1426,plain,
    ( $false
    | spl5_5
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f1398,f165])).

fof(f1398,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_9 ),
    inference(superposition,[],[f48,f1377])).

fof(f1377,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f1375])).

fof(f1375,plain,
    ( spl5_9
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1390,plain,
    ( spl5_9
    | spl5_11 ),
    inference(avatar_split_clause,[],[f1385,f1387,f1375])).

fof(f1385,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1384,f29])).

fof(f1384,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1383,f29])).

fof(f1383,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1354,f495])).

fof(f495,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f490,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f490,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1354,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f1042,f317])).

fof(f317,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),sK2)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X10,X11)
      | ~ r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),X10) ) ),
    inference(resolution,[],[f37,f74])).

fof(f74,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,sK2) ) ),
    inference(superposition,[],[f46,f58])).

fof(f58,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f52])).

fof(f52,plain,(
    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f35,f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1042,plain,(
    ! [X16] :
      ( r2_hidden(sK4(k2_xboole_0(X16,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X16)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X16,sK1)) ) ),
    inference(global_subsumption,[],[f700])).

fof(f700,plain,(
    ! [X17] :
      ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X17,sK1))
      | r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17) ) ),
    inference(forward_demodulation,[],[f699,f29])).

fof(f699,plain,(
    ! [X17] :
      ( r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f682,f495])).

fof(f682,plain,(
    ! [X17] :
      ( r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X17,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f630])).

fof(f630,plain,(
    ! [X17] :
      ( r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X17,sK1)) ) ),
    inference(resolution,[],[f504,f316])).

fof(f316,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),sK1)
      | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X8,X9)
      | ~ r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),X8) ) ),
    inference(resolution,[],[f37,f75])).

fof(f75,plain,(
    ! [X9] :
      ( r2_hidden(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X9,sK1) ) ),
    inference(superposition,[],[f46,f59])).

fof(f59,plain,(
    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f53])).

fof(f53,plain,(
    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f35,f22])).

fof(f504,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3)
      | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2)
      | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4 ) ),
    inference(resolution,[],[f495,f47])).

fof(f155,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f146,f152,f148])).

fof(f146,plain,
    ( r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f145,f21])).

fof(f145,plain,(
    ! [X0] :
      ( v1_tops_2(X0,sK0)
      | r2_hidden(sK3(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (25573)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.46  % (25557)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (25570)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (25552)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (25550)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (25550)Refutation not found, incomplete strategy% (25550)------------------------------
% 0.20/0.50  % (25550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25571)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (25550)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25550)Memory used [KB]: 10618
% 0.20/0.50  % (25550)Time elapsed: 0.087 s
% 0.20/0.50  % (25550)------------------------------
% 0.20/0.50  % (25550)------------------------------
% 0.20/0.50  % (25554)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (25553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (25555)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (25555)Refutation not found, incomplete strategy% (25555)------------------------------
% 0.20/0.50  % (25555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25555)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25555)Memory used [KB]: 10618
% 0.20/0.50  % (25555)Time elapsed: 0.061 s
% 0.20/0.50  % (25555)------------------------------
% 0.20/0.50  % (25555)------------------------------
% 0.20/0.50  % (25562)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (25572)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (25559)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (25551)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (25567)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (25569)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (25568)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (25549)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (25561)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (25560)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (25566)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (25560)Refutation not found, incomplete strategy% (25560)------------------------------
% 0.20/0.52  % (25560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25560)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25560)Memory used [KB]: 10618
% 0.20/0.52  % (25560)Time elapsed: 0.116 s
% 0.20/0.52  % (25560)------------------------------
% 0.20/0.52  % (25560)------------------------------
% 0.20/0.52  % (25554)Refutation not found, incomplete strategy% (25554)------------------------------
% 0.20/0.52  % (25554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25554)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25554)Memory used [KB]: 6140
% 0.20/0.52  % (25554)Time elapsed: 0.087 s
% 0.20/0.52  % (25554)------------------------------
% 0.20/0.52  % (25554)------------------------------
% 0.20/0.52  % (25558)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (25562)Refutation not found, incomplete strategy% (25562)------------------------------
% 0.20/0.52  % (25562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25562)Memory used [KB]: 6268
% 0.20/0.52  % (25562)Time elapsed: 0.101 s
% 0.20/0.52  % (25562)------------------------------
% 0.20/0.52  % (25562)------------------------------
% 0.20/0.53  % (25574)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (25556)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (25564)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (25565)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (25549)Refutation not found, incomplete strategy% (25549)------------------------------
% 0.20/0.54  % (25549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25549)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25549)Memory used [KB]: 10746
% 0.20/0.54  % (25549)Time elapsed: 0.111 s
% 0.20/0.54  % (25549)------------------------------
% 0.20/0.54  % (25549)------------------------------
% 0.20/0.54  % (25563)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (25556)Refutation not found, incomplete strategy% (25556)------------------------------
% 0.20/0.54  % (25556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25556)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25556)Memory used [KB]: 1791
% 0.20/0.54  % (25556)Time elapsed: 0.146 s
% 0.20/0.54  % (25556)------------------------------
% 0.20/0.54  % (25556)------------------------------
% 0.20/0.58  % (25571)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1585,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f155,f1390,f1427,f1485,f1576,f1580,f1584])).
% 0.20/0.58  fof(f1584,plain,(
% 0.20/0.58    ~spl5_5 | ~spl5_23),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1583])).
% 0.20/0.58  fof(f1583,plain,(
% 0.20/0.58    $false | (~spl5_5 | ~spl5_23)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1582,f167])).
% 0.20/0.58  fof(f167,plain,(
% 0.20/0.58    ~v1_tops_2(k2_xboole_0(sK1,sK2),sK0)),
% 0.20/0.58    inference(backward_demodulation,[],[f21,f162])).
% 0.20/0.58  fof(f162,plain,(
% 0.20/0.58    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.20/0.58    inference(resolution,[],[f158,f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.58    inference(flattening,[],[f11])).
% 0.20/0.58  fof(f11,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v1_tops_2(X2,X0) & v1_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,negated_conjecture,(
% 0.20/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.58    inference(negated_conjecture,[],[f9])).
% 0.20/0.58  fof(f9,conjecture,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).
% 0.20/0.58  fof(f158,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k2_xboole_0(X0,sK2)) )),
% 0.20/0.58    inference(resolution,[],[f36,f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(flattening,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f1582,plain,(
% 0.20/0.58    v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl5_5 | ~spl5_23)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1581,f1523])).
% 0.20/0.58  fof(f1523,plain,(
% 0.20/0.58    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_5),
% 0.20/0.58    inference(forward_demodulation,[],[f149,f162])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f148])).
% 0.20/0.58  fof(f148,plain,(
% 0.20/0.58    spl5_5 <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.58  fof(f1581,plain,(
% 0.20/0.58    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~spl5_23),
% 0.20/0.58    inference(resolution,[],[f1575,f466])).
% 0.20/0.58  fof(f466,plain,(
% 0.20/0.58    ( ! [X1] : (~r2_hidden(sK3(sK0,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f460,f18])).
% 0.20/0.58  fof(f460,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0)) )),
% 0.20/0.58    inference(resolution,[],[f458,f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    v1_tops_2(sK2,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f458,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f457,f454])).
% 0.20/0.58  fof(f454,plain,(
% 0.20/0.58    ( ! [X0] : (v1_tops_2(X0,sK0) | m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.58    inference(resolution,[],[f25,f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    l1_pre_topc(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(flattening,[],[f13])).
% 0.20/0.58  fof(f13,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.58  fof(f457,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(resolution,[],[f456,f157])).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    ( ! [X0] : (~v3_pre_topc(sK3(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(resolution,[],[f27,f23])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f456,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(resolution,[],[f24,f23])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v3_pre_topc(X2,X0) | ~v1_tops_2(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f1575,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | ~spl5_23),
% 0.20/0.58    inference(avatar_component_clause,[],[f1573])).
% 0.20/0.58  fof(f1573,plain,(
% 0.20/0.58    spl5_23 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.58  fof(f1580,plain,(
% 0.20/0.58    ~spl5_5 | ~spl5_22),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1579])).
% 0.20/0.58  fof(f1579,plain,(
% 0.20/0.58    $false | (~spl5_5 | ~spl5_22)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1578,f167])).
% 0.20/0.58  fof(f1578,plain,(
% 0.20/0.58    v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl5_5 | ~spl5_22)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1577,f1523])).
% 0.20/0.58  fof(f1577,plain,(
% 0.20/0.58    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~spl5_22),
% 0.20/0.58    inference(resolution,[],[f1571,f465])).
% 0.20/0.58  fof(f465,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f459,f22])).
% 0.20/0.58  fof(f459,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.20/0.58    inference(resolution,[],[f458,f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    v1_tops_2(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f1571,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | ~spl5_22),
% 0.20/0.58    inference(avatar_component_clause,[],[f1569])).
% 0.20/0.58  fof(f1569,plain,(
% 0.20/0.58    spl5_22 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.58  fof(f1576,plain,(
% 0.20/0.58    spl5_22 | spl5_23 | ~spl5_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f1567,f152,f1573,f1569])).
% 0.20/0.58  fof(f152,plain,(
% 0.20/0.58    spl5_6 <=> r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.58  fof(f1567,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | ~spl5_6),
% 0.20/0.58    inference(resolution,[],[f1522,f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.58  fof(f1522,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | ~spl5_6),
% 0.20/0.58    inference(forward_demodulation,[],[f154,f162])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) | ~spl5_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f152])).
% 0.20/0.58  fof(f1485,plain,(
% 0.20/0.58    spl5_5 | ~spl5_11),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1484])).
% 0.20/0.58  fof(f1484,plain,(
% 0.20/0.58    $false | (spl5_5 | ~spl5_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1446,f165])).
% 0.20/0.58  fof(f165,plain,(
% 0.20/0.58    ~r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_5),
% 0.20/0.58    inference(backward_demodulation,[],[f156,f162])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    ~r1_tarski(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_5),
% 0.20/0.58    inference(resolution,[],[f150,f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f150,plain,(
% 0.20/0.58    ~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f148])).
% 0.20/0.58  fof(f1446,plain,(
% 0.20/0.58    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_11),
% 0.20/0.58    inference(superposition,[],[f28,f1389])).
% 0.20/0.58  fof(f1389,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f1387])).
% 0.20/0.58  fof(f1387,plain,(
% 0.20/0.58    spl5_11 <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.58  fof(f1427,plain,(
% 0.20/0.58    spl5_5 | ~spl5_9),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1426])).
% 0.20/0.58  fof(f1426,plain,(
% 0.20/0.58    $false | (spl5_5 | ~spl5_9)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1398,f165])).
% 0.20/0.58  fof(f1398,plain,(
% 0.20/0.58    r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_9),
% 0.20/0.58    inference(superposition,[],[f48,f1377])).
% 0.20/0.58  fof(f1377,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) | ~spl5_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f1375])).
% 0.20/0.58  fof(f1375,plain,(
% 0.20/0.58    spl5_9 <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(superposition,[],[f28,f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.58  fof(f1390,plain,(
% 0.20/0.58    spl5_9 | spl5_11),
% 0.20/0.58    inference(avatar_split_clause,[],[f1385,f1387,f1375])).
% 0.20/0.58  fof(f1385,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))),
% 0.20/0.58    inference(forward_demodulation,[],[f1384,f29])).
% 0.20/0.58  fof(f1384,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(forward_demodulation,[],[f1383,f29])).
% 0.20/0.58  fof(f1383,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(subsumption_resolution,[],[f1354,f495])).
% 0.20/0.58  fof(f495,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f490,f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f490,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.58    inference(factoring,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f1354,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(sK2,sK1))),
% 0.20/0.58    inference(resolution,[],[f1042,f317])).
% 0.20/0.58  fof(f317,plain,(
% 0.20/0.58    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),sK2) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X10,X11) | ~r2_hidden(sK4(X10,X11,k1_zfmisc_1(u1_struct_0(sK0))),X10)) )),
% 0.20/0.58    inference(resolution,[],[f37,f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X8] : (r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X8,sK2)) )),
% 0.20/0.58    inference(superposition,[],[f46,f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(resolution,[],[f30,f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(resolution,[],[f35,f18])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f1042,plain,(
% 0.20/0.58    ( ! [X16] : (r2_hidden(sK4(k2_xboole_0(X16,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X16) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X16,sK1))) )),
% 0.20/0.58    inference(global_subsumption,[],[f700])).
% 0.20/0.58  fof(f700,plain,(
% 0.20/0.58    ( ! [X17] : (k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(X17,sK1)) | r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f699,f29])).
% 0.20/0.58  fof(f699,plain,(
% 0.20/0.58    ( ! [X17] : (r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f682,f495])).
% 0.20/0.58  fof(f682,plain,(
% 0.20/0.58    ( ! [X17] : (r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X17,sK1))) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f630])).
% 0.20/0.58  fof(f630,plain,(
% 0.20/0.58    ( ! [X17] : (r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),X17) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(k2_xboole_0(X17,sK1),k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))),k2_xboole_0(X17,sK1))) )),
% 0.20/0.58    inference(resolution,[],[f504,f316])).
% 0.20/0.58  fof(f316,plain,(
% 0.20/0.58    ( ! [X8,X9] : (~r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),sK1) | k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(X8,X9) | ~r2_hidden(sK4(X8,X9,k1_zfmisc_1(u1_struct_0(sK0))),X8)) )),
% 0.20/0.58    inference(resolution,[],[f37,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X9] : (r2_hidden(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X9,sK1)) )),
% 0.20/0.58    inference(superposition,[],[f46,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(resolution,[],[f30,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(resolution,[],[f35,f22])).
% 0.20/0.58  fof(f504,plain,(
% 0.20/0.58    ( ! [X4,X2,X3] : (r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X3) | r2_hidden(sK4(k2_xboole_0(X2,X3),X4,X4),X2) | k2_xboole_0(k2_xboole_0(X2,X3),X4) = X4) )),
% 0.20/0.58    inference(resolution,[],[f495,f47])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    ~spl5_5 | spl5_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f146,f152,f148])).
% 0.20/0.58  fof(f146,plain,(
% 0.20/0.58    r2_hidden(sK3(sK0,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) | ~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.58    inference(resolution,[],[f145,f21])).
% 0.20/0.58  fof(f145,plain,(
% 0.20/0.58    ( ! [X0] : (v1_tops_2(X0,sK0) | r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.58    inference(resolution,[],[f26,f23])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (25571)------------------------------
% 0.20/0.58  % (25571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (25571)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (25571)Memory used [KB]: 11513
% 0.20/0.58  % (25571)Time elapsed: 0.123 s
% 0.20/0.58  % (25571)------------------------------
% 0.20/0.58  % (25571)------------------------------
% 0.20/0.58  % (25547)Success in time 0.217 s
%------------------------------------------------------------------------------
