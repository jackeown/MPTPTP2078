%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:12 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 201 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  289 ( 489 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f942,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f77,f231,f407,f595,f623,f642,f653,f658,f664,f669,f744,f761,f913,f926])).

fof(f926,plain,(
    spl3_64 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | spl3_64 ),
    inference(unit_resulting_resolution,[],[f48,f912,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f912,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | spl3_64 ),
    inference(avatar_component_clause,[],[f910])).

fof(f910,plain,
    ( spl3_64
  <=> r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f913,plain,
    ( ~ spl3_4
    | ~ spl3_64
    | ~ spl3_1
    | spl3_48 ),
    inference(avatar_split_clause,[],[f902,f758,f51,f910,f66])).

fof(f66,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f758,plain,
    ( spl3_48
  <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f902,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_48 ),
    inference(resolution,[],[f760,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_tops_1(X1,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f33,plain,(
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

fof(f760,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f758])).

fof(f761,plain,
    ( ~ spl3_48
    | spl3_45 ),
    inference(avatar_split_clause,[],[f751,f741,f758])).

fof(f741,plain,
    ( spl3_45
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f751,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_45 ),
    inference(resolution,[],[f743,f36])).

fof(f36,plain,(
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

fof(f743,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f741])).

fof(f744,plain,
    ( ~ spl3_34
    | ~ spl3_45
    | ~ spl3_1
    | spl3_32 ),
    inference(avatar_split_clause,[],[f734,f639,f51,f741,f650])).

fof(f650,plain,
    ( spl3_34
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f639,plain,
    ( spl3_32
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f734,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_32 ),
    inference(resolution,[],[f641,f180])).

fof(f641,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f639])).

fof(f669,plain,
    ( ~ spl3_5
    | spl3_35 ),
    inference(avatar_split_clause,[],[f667,f661,f74])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f661,plain,
    ( spl3_35
  <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f667,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_35 ),
    inference(superposition,[],[f665,f84])).

fof(f84,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f665,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))
    | spl3_35 ),
    inference(resolution,[],[f663,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f663,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f661])).

fof(f664,plain,
    ( ~ spl3_35
    | spl3_34 ),
    inference(avatar_split_clause,[],[f659,f650,f661])).

fof(f659,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_34 ),
    inference(resolution,[],[f652,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f652,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f650])).

fof(f658,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | spl3_33 ),
    inference(unit_resulting_resolution,[],[f35,f648])).

fof(f648,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl3_33
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f653,plain,
    ( ~ spl3_1
    | ~ spl3_33
    | ~ spl3_2
    | ~ spl3_34
    | spl3_31 ),
    inference(avatar_split_clause,[],[f643,f635,f650,f56,f646,f51])).

fof(f56,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f635,plain,
    ( spl3_31
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f643,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_31 ),
    inference(resolution,[],[f637,f34])).

fof(f34,plain,(
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

fof(f637,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f635])).

fof(f642,plain,
    ( ~ spl3_31
    | ~ spl3_32
    | spl3_29 ),
    inference(avatar_split_clause,[],[f632,f620,f639,f635])).

fof(f620,plain,
    ( spl3_29
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f632,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_29 ),
    inference(resolution,[],[f622,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f622,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f620])).

fof(f623,plain,
    ( ~ spl3_29
    | spl3_13
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f615,f584,f228,f620])).

fof(f228,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f584,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f615,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f230,f605])).

fof(f605,plain,
    ( ! [X6] : k4_xboole_0(k1_tops_1(sK0,sK1),X6) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X6)
    | ~ spl3_26 ),
    inference(resolution,[],[f585,f222])).

fof(f222,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f44,f41])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f585,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f584])).

fof(f230,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f228])).

fof(f595,plain,
    ( ~ spl3_5
    | ~ spl3_14
    | spl3_26 ),
    inference(avatar_split_clause,[],[f593,f584,f404,f74])).

fof(f404,plain,
    ( spl3_14
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f593,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_14
    | spl3_26 ),
    inference(superposition,[],[f588,f406])).

fof(f406,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f404])).

fof(f588,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
    | spl3_26 ),
    inference(resolution,[],[f586,f45])).

fof(f586,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f584])).

fof(f407,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f400,f56,f51,f404])).

fof(f400,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f399,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f183,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f183,plain,(
    ! [X8,X7] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | k2_xboole_0(k1_tops_1(X8,X7),X7) = X7 ) ),
    inference(resolution,[],[f33,f37])).

fof(f231,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f226,f61,f56,f228])).

fof(f61,plain,
    ( spl3_3
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f226,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f63,f220])).

fof(f220,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f58])).

fof(f63,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f56,f74])).

fof(f70,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
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

fof(f64,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (7623)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (7631)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (7617)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (7625)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (7617)Refutation not found, incomplete strategy% (7617)------------------------------
% 0.20/0.51  % (7617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7617)Memory used [KB]: 10618
% 0.20/0.51  % (7617)Time elapsed: 0.071 s
% 0.20/0.51  % (7617)------------------------------
% 0.20/0.51  % (7617)------------------------------
% 0.20/0.51  % (7624)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (7619)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (7612)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7616)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (7636)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (7613)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (7614)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (7634)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (7627)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (7615)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (7626)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (7628)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (7633)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (7635)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (7632)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (7618)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (7629)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.55  % (7630)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.55  % (7620)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.51/0.55  % (7621)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.51/0.55  % (7622)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.51/0.56  % (7611)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.66/0.59  % (7626)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f942,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f77,f231,f407,f595,f623,f642,f653,f658,f664,f669,f744,f761,f913,f926])).
% 1.66/0.59  fof(f926,plain,(
% 1.66/0.59    spl3_64),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f919])).
% 1.66/0.59  fof(f919,plain,(
% 1.66/0.59    $false | spl3_64),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f48,f912,f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.66/0.59  fof(f912,plain,(
% 1.66/0.59    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | spl3_64),
% 1.66/0.59    inference(avatar_component_clause,[],[f910])).
% 1.66/0.59  fof(f910,plain,(
% 1.66/0.59    spl3_64 <=> r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.59    inference(equality_resolution,[],[f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f2])).
% 1.66/0.59  fof(f2,axiom,(
% 1.66/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.59  fof(f913,plain,(
% 1.66/0.59    ~spl3_4 | ~spl3_64 | ~spl3_1 | spl3_48),
% 1.66/0.59    inference(avatar_split_clause,[],[f902,f758,f51,f910,f66])).
% 1.66/0.59  fof(f66,plain,(
% 1.66/0.59    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.66/0.59  fof(f51,plain,(
% 1.66/0.59    spl3_1 <=> l1_pre_topc(sK0)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.66/0.59  fof(f758,plain,(
% 1.66/0.59    spl3_48 <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.66/0.59  fof(f902,plain,(
% 1.66/0.59    ~l1_pre_topc(sK0) | ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_48),
% 1.66/0.59    inference(resolution,[],[f760,f180])).
% 1.66/0.59  fof(f180,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(k1_tops_1(X1,X0),X2) | ~l1_pre_topc(X1) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.59    inference(resolution,[],[f33,f46])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(flattening,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.66/0.59  fof(f760,plain,(
% 1.66/0.59    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_48),
% 1.66/0.59    inference(avatar_component_clause,[],[f758])).
% 1.66/0.59  fof(f761,plain,(
% 1.66/0.59    ~spl3_48 | spl3_45),
% 1.66/0.59    inference(avatar_split_clause,[],[f751,f741,f758])).
% 1.66/0.59  fof(f741,plain,(
% 1.66/0.59    spl3_45 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.66/0.59  fof(f751,plain,(
% 1.66/0.59    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_45),
% 1.66/0.59    inference(resolution,[],[f743,f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.66/0.59  fof(f743,plain,(
% 1.66/0.59    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | spl3_45),
% 1.66/0.59    inference(avatar_component_clause,[],[f741])).
% 1.66/0.59  fof(f744,plain,(
% 1.66/0.59    ~spl3_34 | ~spl3_45 | ~spl3_1 | spl3_32),
% 1.66/0.59    inference(avatar_split_clause,[],[f734,f639,f51,f741,f650])).
% 1.66/0.59  fof(f650,plain,(
% 1.66/0.59    spl3_34 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.66/0.59  fof(f639,plain,(
% 1.66/0.59    spl3_32 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.66/0.59  fof(f734,plain,(
% 1.66/0.59    ~l1_pre_topc(sK0) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_32),
% 1.66/0.59    inference(resolution,[],[f641,f180])).
% 1.66/0.59  fof(f641,plain,(
% 1.66/0.59    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_32),
% 1.66/0.59    inference(avatar_component_clause,[],[f639])).
% 1.66/0.59  fof(f669,plain,(
% 1.66/0.59    ~spl3_5 | spl3_35),
% 1.66/0.59    inference(avatar_split_clause,[],[f667,f661,f74])).
% 1.66/0.59  fof(f74,plain,(
% 1.66/0.59    spl3_5 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.66/0.59  fof(f661,plain,(
% 1.66/0.59    spl3_35 <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.66/0.59  fof(f667,plain,(
% 1.66/0.59    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_35),
% 1.66/0.59    inference(superposition,[],[f665,f84])).
% 1.66/0.59  fof(f84,plain,(
% 1.66/0.59    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) )),
% 1.66/0.59    inference(resolution,[],[f37,f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.66/0.59  fof(f665,plain,(
% 1.66/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))) ) | spl3_35),
% 1.66/0.59    inference(resolution,[],[f663,f45])).
% 1.66/0.59  fof(f45,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.66/0.59    inference(ennf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.66/0.59  fof(f663,plain,(
% 1.66/0.59    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_35),
% 1.66/0.59    inference(avatar_component_clause,[],[f661])).
% 1.66/0.59  fof(f664,plain,(
% 1.66/0.59    ~spl3_35 | spl3_34),
% 1.66/0.59    inference(avatar_split_clause,[],[f659,f650,f661])).
% 1.66/0.59  fof(f659,plain,(
% 1.66/0.59    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_34),
% 1.66/0.59    inference(resolution,[],[f652,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.59  fof(f652,plain,(
% 1.66/0.59    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_34),
% 1.66/0.59    inference(avatar_component_clause,[],[f650])).
% 1.66/0.59  fof(f658,plain,(
% 1.66/0.59    spl3_33),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f654])).
% 1.66/0.59  fof(f654,plain,(
% 1.66/0.59    $false | spl3_33),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f35,f648])).
% 1.66/0.59  fof(f648,plain,(
% 1.66/0.59    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_33),
% 1.66/0.59    inference(avatar_component_clause,[],[f646])).
% 1.66/0.59  fof(f646,plain,(
% 1.66/0.59    spl3_33 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.66/0.59  fof(f653,plain,(
% 1.66/0.59    ~spl3_1 | ~spl3_33 | ~spl3_2 | ~spl3_34 | spl3_31),
% 1.66/0.59    inference(avatar_split_clause,[],[f643,f635,f650,f56,f646,f51])).
% 1.66/0.59  fof(f56,plain,(
% 1.66/0.59    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.66/0.59  fof(f635,plain,(
% 1.66/0.59    spl3_31 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.66/0.59  fof(f643,plain,(
% 1.66/0.59    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl3_31),
% 1.66/0.59    inference(resolution,[],[f637,f34])).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.59    inference(flattening,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.66/0.59  fof(f637,plain,(
% 1.66/0.59    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_31),
% 1.66/0.59    inference(avatar_component_clause,[],[f635])).
% 1.66/0.59  fof(f642,plain,(
% 1.66/0.59    ~spl3_31 | ~spl3_32 | spl3_29),
% 1.66/0.59    inference(avatar_split_clause,[],[f632,f620,f639,f635])).
% 1.66/0.59  fof(f620,plain,(
% 1.66/0.59    spl3_29 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.66/0.59  fof(f632,plain,(
% 1.66/0.59    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_29),
% 1.66/0.59    inference(resolution,[],[f622,f47])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(flattening,[],[f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.66/0.59  fof(f622,plain,(
% 1.66/0.59    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_29),
% 1.66/0.60    inference(avatar_component_clause,[],[f620])).
% 1.66/0.60  fof(f623,plain,(
% 1.66/0.60    ~spl3_29 | spl3_13 | ~spl3_26),
% 1.66/0.60    inference(avatar_split_clause,[],[f615,f584,f228,f620])).
% 1.66/0.60  fof(f228,plain,(
% 1.66/0.60    spl3_13 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.66/0.60  fof(f584,plain,(
% 1.66/0.60    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.66/0.60  fof(f615,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (spl3_13 | ~spl3_26)),
% 1.66/0.60    inference(backward_demodulation,[],[f230,f605])).
% 1.66/0.60  fof(f605,plain,(
% 1.66/0.60    ( ! [X6] : (k4_xboole_0(k1_tops_1(sK0,sK1),X6) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X6)) ) | ~spl3_26),
% 1.66/0.60    inference(resolution,[],[f585,f222])).
% 1.66/0.60  fof(f222,plain,(
% 1.66/0.60    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 1.66/0.60    inference(resolution,[],[f44,f41])).
% 1.66/0.60  fof(f44,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f23])).
% 1.66/0.60  fof(f23,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f9])).
% 1.66/0.60  fof(f9,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.66/0.60  fof(f585,plain,(
% 1.66/0.60    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl3_26),
% 1.66/0.60    inference(avatar_component_clause,[],[f584])).
% 1.66/0.60  fof(f230,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_13),
% 1.66/0.60    inference(avatar_component_clause,[],[f228])).
% 1.66/0.60  fof(f595,plain,(
% 1.66/0.60    ~spl3_5 | ~spl3_14 | spl3_26),
% 1.66/0.60    inference(avatar_split_clause,[],[f593,f584,f404,f74])).
% 1.66/0.60  fof(f404,plain,(
% 1.66/0.60    spl3_14 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.66/0.60  fof(f593,plain,(
% 1.66/0.60    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_14 | spl3_26)),
% 1.66/0.60    inference(superposition,[],[f588,f406])).
% 1.66/0.60  fof(f406,plain,(
% 1.66/0.60    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_14),
% 1.66/0.60    inference(avatar_component_clause,[],[f404])).
% 1.66/0.60  fof(f588,plain,(
% 1.66/0.60    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))) ) | spl3_26),
% 1.66/0.60    inference(resolution,[],[f586,f45])).
% 1.66/0.60  fof(f586,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_26),
% 1.66/0.60    inference(avatar_component_clause,[],[f584])).
% 1.66/0.60  fof(f407,plain,(
% 1.66/0.60    spl3_14 | ~spl3_1 | ~spl3_2),
% 1.66/0.60    inference(avatar_split_clause,[],[f400,f56,f51,f404])).
% 1.66/0.60  fof(f400,plain,(
% 1.66/0.60    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | (~spl3_1 | ~spl3_2)),
% 1.66/0.60    inference(resolution,[],[f399,f58])).
% 1.66/0.60  fof(f58,plain,(
% 1.66/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.66/0.60    inference(avatar_component_clause,[],[f56])).
% 1.66/0.60  fof(f399,plain,(
% 1.66/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0) ) | ~spl3_1),
% 1.66/0.60    inference(resolution,[],[f183,f53])).
% 1.66/0.60  fof(f53,plain,(
% 1.66/0.60    l1_pre_topc(sK0) | ~spl3_1),
% 1.66/0.60    inference(avatar_component_clause,[],[f51])).
% 1.66/0.60  fof(f183,plain,(
% 1.66/0.60    ( ! [X8,X7] : (~l1_pre_topc(X8) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | k2_xboole_0(k1_tops_1(X8,X7),X7) = X7) )),
% 1.66/0.60    inference(resolution,[],[f33,f37])).
% 1.66/0.60  fof(f231,plain,(
% 1.66/0.60    ~spl3_13 | ~spl3_2 | spl3_3),
% 1.66/0.60    inference(avatar_split_clause,[],[f226,f61,f56,f228])).
% 1.66/0.60  fof(f61,plain,(
% 1.66/0.60    spl3_3 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.66/0.60  fof(f226,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (~spl3_2 | spl3_3)),
% 1.66/0.60    inference(backward_demodulation,[],[f63,f220])).
% 1.66/0.60  fof(f220,plain,(
% 1.66/0.60    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_2),
% 1.66/0.60    inference(resolution,[],[f44,f58])).
% 1.66/0.60  fof(f63,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_3),
% 1.66/0.60    inference(avatar_component_clause,[],[f61])).
% 1.66/0.60  fof(f77,plain,(
% 1.66/0.60    spl3_5 | ~spl3_2),
% 1.66/0.60    inference(avatar_split_clause,[],[f70,f56,f74])).
% 1.66/0.60  fof(f70,plain,(
% 1.66/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 1.66/0.60    inference(resolution,[],[f42,f58])).
% 1.66/0.60  fof(f42,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    spl3_4),
% 1.66/0.60    inference(avatar_split_clause,[],[f29,f66])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  fof(f16,plain,(
% 1.66/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,plain,(
% 1.66/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.60    inference(pure_predicate_removal,[],[f14])).
% 1.66/0.60  fof(f14,negated_conjecture,(
% 1.66/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.60    inference(negated_conjecture,[],[f13])).
% 1.66/0.60  fof(f13,conjecture,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 1.66/0.60  fof(f64,plain,(
% 1.66/0.60    ~spl3_3),
% 1.66/0.60    inference(avatar_split_clause,[],[f30,f61])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  fof(f59,plain,(
% 1.66/0.60    spl3_2),
% 1.66/0.60    inference(avatar_split_clause,[],[f31,f56])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  fof(f54,plain,(
% 1.66/0.60    spl3_1),
% 1.66/0.60    inference(avatar_split_clause,[],[f32,f51])).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    l1_pre_topc(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (7626)------------------------------
% 1.66/0.60  % (7626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (7626)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (7626)Memory used [KB]: 6908
% 1.66/0.60  % (7626)Time elapsed: 0.171 s
% 1.66/0.60  % (7626)------------------------------
% 1.66/0.60  % (7626)------------------------------
% 1.66/0.61  % (7610)Success in time 0.252 s
%------------------------------------------------------------------------------
