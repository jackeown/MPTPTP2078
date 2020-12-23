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
% DateTime   : Thu Dec  3 13:11:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 448 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f204,f229,f1249,f1331,f1770,f1773,f1801,f1855])).

fof(f1855,plain,
    ( ~ spl3_9
    | ~ spl3_38
    | spl3_54 ),
    inference(avatar_split_clause,[],[f1853,f1799,f1310,f187])).

fof(f187,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1310,plain,
    ( spl3_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1799,plain,
    ( spl3_54
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f1853,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_54 ),
    inference(resolution,[],[f1814,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1814,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_54 ),
    inference(resolution,[],[f1813,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1813,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_54 ),
    inference(resolution,[],[f1800,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1800,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f1799])).

fof(f1801,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | ~ spl3_54
    | spl3_51 ),
    inference(avatar_split_clause,[],[f1793,f1768,f1799,f107,f187])).

fof(f107,plain,
    ( spl3_1
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1768,plain,
    ( spl3_51
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f1793,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_51 ),
    inference(resolution,[],[f1774,f35])).

fof(f1774,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0)
        | ~ r1_xboole_0(X0,k1_tops_1(sK0,sK2)) )
    | spl3_51 ),
    inference(resolution,[],[f1769,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1769,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1773,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_35
    | ~ spl3_1
    | spl3_50 ),
    inference(avatar_split_clause,[],[f1771,f1765,f107,f1236,f190,f187])).

fof(f190,plain,
    ( spl3_10
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1236,plain,
    ( spl3_35
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f1765,plain,
    ( spl3_50
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1771,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_50 ),
    inference(resolution,[],[f1766,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1766,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_50 ),
    inference(avatar_component_clause,[],[f1765])).

fof(f1770,plain,
    ( ~ spl3_50
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f1762,f1768,f1765])).

fof(f1762,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1736,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1736,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f64,f1526])).

fof(f1526,plain,(
    ! [X0] : k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
    inference(resolution,[],[f914,f48])).

fof(f48,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f914,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK1,X2)
      | k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(X2,k1_tops_1(sK0,sK1),X3) ) ),
    inference(global_subsumption,[],[f32,f902])).

fof(f902,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK1,X2)
      | k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(X2,k1_tops_1(sK0,sK1),X3)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f145,f31])).

fof(f145,plain,(
    ! [X19,X17,X20,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ r1_tarski(X17,X18)
      | k4_xboole_0(k1_tops_1(X19,X17),X20) = k7_subset_1(X18,k1_tops_1(X19,X17),X20)
      | ~ l1_pre_topc(X19) ) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X5,X4)
      | ~ r1_tarski(X2,X5)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f61,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X6)
      | k4_xboole_0(X4,X5) = k7_subset_1(X6,X4,X5) ) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f30,f59])).

fof(f59,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f42,f31])).

fof(f30,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f1331,plain,(
    spl3_38 ),
    inference(avatar_contradiction_clause,[],[f1329])).

fof(f1329,plain,
    ( $false
    | spl3_38 ),
    inference(resolution,[],[f1311,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f1311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1249,plain,(
    spl3_35 ),
    inference(avatar_contradiction_clause,[],[f1247])).

fof(f1247,plain,
    ( $false
    | spl3_35 ),
    inference(resolution,[],[f1237,f31])).

fof(f1237,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f229,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f191,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f191,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f204,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f188,f32])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f187])).

fof(f171,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f154,f48])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_1 ),
    inference(resolution,[],[f131,f37])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_1 ),
    inference(resolution,[],[f129,f45])).

fof(f129,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_1 ),
    inference(resolution,[],[f108,f39])).

fof(f108,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 19:43:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.46  % (4602)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.47  % (4596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (4607)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.49  % (4592)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.49  % (4614)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.49  % (4603)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.49  % (4604)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.49  % (4594)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.50  % (4609)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.50  % (4606)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.51  % (4595)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.51  % (4600)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.51  % (4591)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.51  % (4610)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.52  % (4605)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.52  % (4593)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.52  % (4612)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.53  % (4598)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (4611)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.53  % (4613)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.54  % (4608)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.54  % (4597)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.54  % (4599)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.55  % (4601)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.59  % (4603)Refutation found. Thanks to Tanya!
% 0.19/0.59  % SZS status Theorem for theBenchmark
% 2.08/0.61  % SZS output start Proof for theBenchmark
% 2.08/0.61  fof(f1856,plain,(
% 2.08/0.61    $false),
% 2.08/0.61    inference(avatar_sat_refutation,[],[f171,f204,f229,f1249,f1331,f1770,f1773,f1801,f1855])).
% 2.08/0.61  fof(f1855,plain,(
% 2.08/0.61    ~spl3_9 | ~spl3_38 | spl3_54),
% 2.08/0.61    inference(avatar_split_clause,[],[f1853,f1799,f1310,f187])).
% 2.08/0.61  fof(f187,plain,(
% 2.08/0.61    spl3_9 <=> l1_pre_topc(sK0)),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.08/0.61  fof(f1310,plain,(
% 2.08/0.61    spl3_38 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 2.08/0.61  fof(f1799,plain,(
% 2.08/0.61    spl3_54 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 2.08/0.61  fof(f1853,plain,(
% 2.08/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_54),
% 2.08/0.61    inference(resolution,[],[f1814,f35])).
% 2.08/0.61  fof(f35,plain,(
% 2.08/0.61    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f17])).
% 2.08/0.61  fof(f17,plain,(
% 2.08/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.61    inference(ennf_transformation,[],[f11])).
% 2.08/0.61  fof(f11,axiom,(
% 2.08/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.08/0.61  fof(f1814,plain,(
% 2.08/0.61    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl3_54),
% 2.08/0.61    inference(resolution,[],[f1813,f41])).
% 2.08/0.61  fof(f41,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f21])).
% 2.08/0.61  fof(f21,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.08/0.61    inference(ennf_transformation,[],[f5])).
% 2.08/0.61  fof(f5,axiom,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.08/0.61  fof(f1813,plain,(
% 2.08/0.61    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_54),
% 2.08/0.61    inference(resolution,[],[f1800,f38])).
% 2.08/0.61  fof(f38,plain,(
% 2.08/0.61    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f20])).
% 2.08/0.61  fof(f20,plain,(
% 2.08/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.08/0.61    inference(ennf_transformation,[],[f1])).
% 2.08/0.61  fof(f1,axiom,(
% 2.08/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.08/0.61  fof(f1800,plain,(
% 2.08/0.61    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | spl3_54),
% 2.08/0.61    inference(avatar_component_clause,[],[f1799])).
% 2.08/0.61  fof(f1801,plain,(
% 2.08/0.61    ~spl3_9 | ~spl3_1 | ~spl3_54 | spl3_51),
% 2.08/0.61    inference(avatar_split_clause,[],[f1793,f1768,f1799,f107,f187])).
% 2.08/0.61  fof(f107,plain,(
% 2.08/0.61    spl3_1 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.08/0.61  fof(f1768,plain,(
% 2.08/0.61    spl3_51 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 2.08/0.61  fof(f1793,plain,(
% 2.08/0.61    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_51),
% 2.08/0.61    inference(resolution,[],[f1774,f35])).
% 2.08/0.61  fof(f1774,plain,(
% 2.08/0.61    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0) | ~r1_xboole_0(X0,k1_tops_1(sK0,sK2))) ) | spl3_51),
% 2.08/0.61    inference(resolution,[],[f1769,f43])).
% 2.08/0.61  fof(f43,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f24])).
% 2.08/0.61  fof(f24,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.61    inference(flattening,[],[f23])).
% 2.08/0.61  fof(f23,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.61    inference(ennf_transformation,[],[f4])).
% 2.08/0.61  fof(f4,axiom,(
% 2.08/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.08/0.61  fof(f1769,plain,(
% 2.08/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_51),
% 2.08/0.61    inference(avatar_component_clause,[],[f1768])).
% 2.08/0.61  fof(f1773,plain,(
% 2.08/0.61    ~spl3_9 | ~spl3_10 | ~spl3_35 | ~spl3_1 | spl3_50),
% 2.08/0.61    inference(avatar_split_clause,[],[f1771,f1765,f107,f1236,f190,f187])).
% 2.08/0.61  fof(f190,plain,(
% 2.08/0.61    spl3_10 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.08/0.61  fof(f1236,plain,(
% 2.08/0.61    spl3_35 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.08/0.61  fof(f1765,plain,(
% 2.08/0.61    spl3_50 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.08/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 2.08/0.61  fof(f1771,plain,(
% 2.08/0.61    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl3_50),
% 2.08/0.61    inference(resolution,[],[f1766,f36])).
% 2.08/0.61  fof(f36,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f19])).
% 2.08/0.61  fof(f19,plain,(
% 2.08/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.61    inference(flattening,[],[f18])).
% 2.08/0.61  fof(f18,plain,(
% 2.08/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.61    inference(ennf_transformation,[],[f12])).
% 2.08/0.61  fof(f12,axiom,(
% 2.08/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.08/0.61  fof(f1766,plain,(
% 2.08/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_50),
% 2.08/0.61    inference(avatar_component_clause,[],[f1765])).
% 2.08/0.61  fof(f1770,plain,(
% 2.08/0.61    ~spl3_50 | ~spl3_51),
% 2.08/0.61    inference(avatar_split_clause,[],[f1762,f1768,f1765])).
% 2.08/0.61  fof(f1762,plain,(
% 2.08/0.61    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.08/0.61    inference(resolution,[],[f1736,f44])).
% 2.08/0.61  fof(f44,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f26])).
% 2.08/0.61  fof(f26,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.61    inference(flattening,[],[f25])).
% 2.08/0.61  fof(f25,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.61    inference(ennf_transformation,[],[f6])).
% 2.08/0.61  fof(f6,axiom,(
% 2.08/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.08/0.61  fof(f1736,plain,(
% 2.08/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.08/0.61    inference(backward_demodulation,[],[f64,f1526])).
% 2.08/0.61  fof(f1526,plain,(
% 2.08/0.61    ( ! [X0] : (k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)) )),
% 2.08/0.61    inference(resolution,[],[f914,f48])).
% 2.08/0.61  fof(f48,plain,(
% 2.08/0.61    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.08/0.61    inference(resolution,[],[f40,f31])).
% 2.08/0.61  fof(f31,plain,(
% 2.08/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.61    inference(cnf_transformation,[],[f16])).
% 2.08/0.61  fof(f16,plain,(
% 2.08/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.08/0.61    inference(ennf_transformation,[],[f15])).
% 2.08/0.61  fof(f15,plain,(
% 2.08/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.08/0.61    inference(pure_predicate_removal,[],[f14])).
% 2.08/0.61  fof(f14,negated_conjecture,(
% 2.08/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.08/0.61    inference(negated_conjecture,[],[f13])).
% 2.08/0.61  fof(f13,conjecture,(
% 2.08/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 2.08/0.61  fof(f40,plain,(
% 2.08/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f10])).
% 2.08/0.61  fof(f10,axiom,(
% 2.08/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.08/0.61  fof(f914,plain,(
% 2.08/0.61    ( ! [X2,X3] : (~r1_tarski(sK1,X2) | k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(X2,k1_tops_1(sK0,sK1),X3)) )),
% 2.08/0.61    inference(global_subsumption,[],[f32,f902])).
% 2.08/0.61  fof(f902,plain,(
% 2.08/0.61    ( ! [X2,X3] : (~r1_tarski(sK1,X2) | k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(X2,k1_tops_1(sK0,sK1),X3) | ~l1_pre_topc(sK0)) )),
% 2.08/0.61    inference(resolution,[],[f145,f31])).
% 2.08/0.61  fof(f145,plain,(
% 2.08/0.61    ( ! [X19,X17,X20,X18] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X19))) | ~r1_tarski(X17,X18) | k4_xboole_0(k1_tops_1(X19,X17),X20) = k7_subset_1(X18,k1_tops_1(X19,X17),X20) | ~l1_pre_topc(X19)) )),
% 2.08/0.61    inference(resolution,[],[f73,f35])).
% 2.08/0.61  fof(f73,plain,(
% 2.08/0.61    ( ! [X4,X2,X5,X3] : (~r1_tarski(X5,X4) | ~r1_tarski(X2,X5) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 2.08/0.61    inference(resolution,[],[f61,f45])).
% 2.08/0.61  fof(f45,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f28])).
% 2.08/0.61  fof(f28,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.61    inference(flattening,[],[f27])).
% 2.08/0.61  fof(f27,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.61    inference(ennf_transformation,[],[f2])).
% 2.08/0.61  fof(f2,axiom,(
% 2.08/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.08/0.61  fof(f61,plain,(
% 2.08/0.61    ( ! [X6,X4,X5] : (~r1_tarski(X4,X6) | k4_xboole_0(X4,X5) = k7_subset_1(X6,X4,X5)) )),
% 2.08/0.61    inference(resolution,[],[f42,f39])).
% 2.08/0.61  fof(f39,plain,(
% 2.08/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f10])).
% 2.08/0.61  fof(f42,plain,(
% 2.08/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f22])).
% 2.08/0.61  fof(f22,plain,(
% 2.08/0.61    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.61    inference(ennf_transformation,[],[f9])).
% 2.08/0.61  fof(f9,axiom,(
% 2.08/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.08/0.61  fof(f32,plain,(
% 2.08/0.61    l1_pre_topc(sK0)),
% 2.08/0.61    inference(cnf_transformation,[],[f16])).
% 2.08/0.61  fof(f64,plain,(
% 2.08/0.61    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.08/0.61    inference(backward_demodulation,[],[f30,f59])).
% 2.08/0.61  fof(f59,plain,(
% 2.08/0.61    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 2.08/0.61    inference(resolution,[],[f42,f31])).
% 2.08/0.61  fof(f30,plain,(
% 2.08/0.61    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.08/0.61    inference(cnf_transformation,[],[f16])).
% 2.08/0.61  fof(f1331,plain,(
% 2.08/0.61    spl3_38),
% 2.08/0.61    inference(avatar_contradiction_clause,[],[f1329])).
% 2.08/0.61  fof(f1329,plain,(
% 2.08/0.61    $false | spl3_38),
% 2.08/0.61    inference(resolution,[],[f1311,f29])).
% 2.08/0.61  fof(f29,plain,(
% 2.08/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.61    inference(cnf_transformation,[],[f16])).
% 2.08/0.61  fof(f1311,plain,(
% 2.08/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_38),
% 2.08/0.61    inference(avatar_component_clause,[],[f1310])).
% 2.08/0.61  fof(f1249,plain,(
% 2.08/0.61    spl3_35),
% 2.08/0.61    inference(avatar_contradiction_clause,[],[f1247])).
% 2.08/0.61  fof(f1247,plain,(
% 2.08/0.61    $false | spl3_35),
% 2.08/0.61    inference(resolution,[],[f1237,f31])).
% 2.08/0.61  fof(f1237,plain,(
% 2.08/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_35),
% 2.08/0.61    inference(avatar_component_clause,[],[f1236])).
% 2.08/0.61  fof(f229,plain,(
% 2.08/0.61    spl3_10),
% 2.08/0.61    inference(avatar_contradiction_clause,[],[f227])).
% 2.08/0.61  fof(f227,plain,(
% 2.08/0.61    $false | spl3_10),
% 2.08/0.61    inference(resolution,[],[f191,f37])).
% 2.08/0.61  fof(f37,plain,(
% 2.08/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.08/0.61    inference(cnf_transformation,[],[f3])).
% 2.08/0.61  fof(f3,axiom,(
% 2.08/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.08/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.08/0.61  fof(f191,plain,(
% 2.08/0.61    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_10),
% 2.08/0.61    inference(avatar_component_clause,[],[f190])).
% 2.08/0.61  fof(f204,plain,(
% 2.08/0.61    spl3_9),
% 2.08/0.61    inference(avatar_contradiction_clause,[],[f203])).
% 2.08/0.61  fof(f203,plain,(
% 2.08/0.61    $false | spl3_9),
% 2.08/0.61    inference(resolution,[],[f188,f32])).
% 2.08/0.61  fof(f188,plain,(
% 2.08/0.61    ~l1_pre_topc(sK0) | spl3_9),
% 2.08/0.61    inference(avatar_component_clause,[],[f187])).
% 2.08/0.61  fof(f171,plain,(
% 2.08/0.61    spl3_1),
% 2.08/0.61    inference(avatar_contradiction_clause,[],[f169])).
% 2.08/0.61  fof(f169,plain,(
% 2.08/0.61    $false | spl3_1),
% 2.08/0.61    inference(resolution,[],[f154,f48])).
% 2.08/0.61  fof(f154,plain,(
% 2.08/0.61    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_1),
% 2.08/0.61    inference(resolution,[],[f131,f37])).
% 2.08/0.61  fof(f131,plain,(
% 2.08/0.61    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_1),
% 2.08/0.61    inference(resolution,[],[f129,f45])).
% 2.08/0.61  fof(f129,plain,(
% 2.08/0.61    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_1),
% 2.08/0.61    inference(resolution,[],[f108,f39])).
% 2.08/0.61  fof(f108,plain,(
% 2.08/0.61    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 2.08/0.61    inference(avatar_component_clause,[],[f107])).
% 2.08/0.61  % SZS output end Proof for theBenchmark
% 2.08/0.61  % (4603)------------------------------
% 2.08/0.61  % (4603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.61  % (4603)Termination reason: Refutation
% 2.08/0.61  
% 2.08/0.61  % (4603)Memory used [KB]: 12537
% 2.08/0.61  % (4603)Time elapsed: 0.182 s
% 2.08/0.61  % (4603)------------------------------
% 2.08/0.61  % (4603)------------------------------
% 2.08/0.61  % (4590)Success in time 0.273 s
%------------------------------------------------------------------------------
