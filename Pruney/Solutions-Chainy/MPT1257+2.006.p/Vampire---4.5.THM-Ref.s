%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 185 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :    6
%              Number of atoms          :  269 ( 459 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f959,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f62,f68,f121,f166,f193,f215,f243,f249,f275,f333,f340,f748,f938])).

fof(f938,plain,
    ( ~ spl2_43
    | spl2_1
    | ~ spl2_5
    | ~ spl2_105 ),
    inference(avatar_split_clause,[],[f753,f745,f65,f43,f337])).

fof(f337,plain,
    ( spl2_43
  <=> r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f43,plain,
    ( spl2_1
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( spl2_5
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f745,plain,
    ( spl2_105
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f753,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_105 ),
    inference(unit_resulting_resolution,[],[f45,f67,f747,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f747,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_105 ),
    inference(avatar_component_clause,[],[f745])).

fof(f67,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f45,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f748,plain,
    ( ~ spl2_30
    | spl2_105
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f731,f330,f745,f246])).

fof(f246,plain,
    ( spl2_30
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f330,plain,
    ( spl2_42
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f731,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_42 ),
    inference(superposition,[],[f41,f332])).

fof(f332,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f330])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f340,plain,
    ( spl2_43
    | ~ spl2_32
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f334,f330,f272,f337])).

fof(f272,plain,
    ( spl2_32
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f334,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_32
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f274,f332])).

fof(f274,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f333,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f315,f53,f48,f330])).

fof(f48,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f53,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f315,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f55,f50,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f275,plain,
    ( spl2_32
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f270,f227,f65,f59,f272])).

fof(f59,plain,
    ( spl2_4
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f227,plain,
    ( spl2_27
  <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f270,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f257,f229])).

fof(f229,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f257,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f61,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f61,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f249,plain,
    ( spl2_30
    | ~ spl2_17
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f244,f227,f163,f246])).

fof(f163,plain,
    ( spl2_17
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f244,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_17
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f165,f229])).

fof(f165,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f243,plain,
    ( spl2_27
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f242,f212,f184,f227])).

fof(f184,plain,
    ( spl2_21
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f212,plain,
    ( spl2_24
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f242,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_21
    | ~ spl2_24 ),
    inference(backward_demodulation,[],[f186,f214])).

fof(f214,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f212])).

fof(f186,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f184])).

fof(f215,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f210,f118,f59,f53,f212])).

fof(f118,plain,
    ( spl2_13
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f210,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f208,f120])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f208,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f55,f61,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f193,plain,
    ( spl2_21
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f140,f65,f59,f184])).

fof(f140,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f61,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f166,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f149,f65,f59,f163])).

fof(f149,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f61,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f121,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f109,f53,f48,f118])).

fof(f109,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f55,f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f68,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f63,f53,f48,f65])).

fof(f63,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f55,f50,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f62,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f57,f48,f59])).

fof(f57,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f50,f41])).

fof(f56,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f51,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f31,f43])).

fof(f31,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:59:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (15209)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.44  % (15226)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.47  % (15218)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.47  % (15204)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.47  % (15208)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.48  % (15206)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.48  % (15205)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.48  % (15210)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.48  % (15228)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.48  % (15220)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.49  % (15223)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.49  % (15228)Refutation not found, incomplete strategy% (15228)------------------------------
% 0.19/0.49  % (15228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (15215)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.49  % (15211)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (15228)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (15228)Memory used [KB]: 10618
% 0.19/0.49  % (15228)Time elapsed: 0.054 s
% 0.19/0.49  % (15228)------------------------------
% 0.19/0.49  % (15228)------------------------------
% 0.19/0.49  % (15215)Refutation not found, incomplete strategy% (15215)------------------------------
% 0.19/0.49  % (15215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (15219)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.49  % (15225)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.49  % (15216)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.49  % (15222)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.49  % (15210)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (15217)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (15227)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.50  % (15214)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.50  % (15224)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.50  % (15207)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.50  % (15212)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.50  % (15207)Refutation not found, incomplete strategy% (15207)------------------------------
% 0.19/0.50  % (15207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15221)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.50  % (15207)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15207)Memory used [KB]: 10490
% 0.19/0.50  % (15207)Time elapsed: 0.100 s
% 0.19/0.50  % (15207)------------------------------
% 0.19/0.50  % (15207)------------------------------
% 0.19/0.51  % (15215)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (15215)Memory used [KB]: 10618
% 0.19/0.51  % (15215)Time elapsed: 0.101 s
% 0.19/0.51  % (15215)------------------------------
% 0.19/0.51  % (15215)------------------------------
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f959,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f46,f51,f56,f62,f68,f121,f166,f193,f215,f243,f249,f275,f333,f340,f748,f938])).
% 0.19/0.51  fof(f938,plain,(
% 0.19/0.51    ~spl2_43 | spl2_1 | ~spl2_5 | ~spl2_105),
% 0.19/0.51    inference(avatar_split_clause,[],[f753,f745,f65,f43,f337])).
% 0.19/0.51  fof(f337,plain,(
% 0.19/0.51    spl2_43 <=> r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    spl2_1 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    spl2_5 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.51  fof(f745,plain,(
% 0.19/0.51    spl2_105 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).
% 0.19/0.51  fof(f753,plain,(
% 0.19/0.51    ~r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (spl2_1 | ~spl2_5 | ~spl2_105)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f45,f67,f747,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.19/0.51  fof(f747,plain,(
% 0.19/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_105),
% 0.19/0.51    inference(avatar_component_clause,[],[f745])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f65])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | spl2_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f43])).
% 0.19/0.51  fof(f748,plain,(
% 0.19/0.51    ~spl2_30 | spl2_105 | ~spl2_42),
% 0.19/0.51    inference(avatar_split_clause,[],[f731,f330,f745,f246])).
% 0.19/0.51  fof(f246,plain,(
% 0.19/0.51    spl2_30 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.19/0.51  fof(f330,plain,(
% 0.19/0.51    spl2_42 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.19/0.51  fof(f731,plain,(
% 0.19/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_42),
% 0.19/0.51    inference(superposition,[],[f41,f332])).
% 0.19/0.51  fof(f332,plain,(
% 0.19/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_42),
% 0.19/0.51    inference(avatar_component_clause,[],[f330])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.51  fof(f340,plain,(
% 0.19/0.51    spl2_43 | ~spl2_32 | ~spl2_42),
% 0.19/0.51    inference(avatar_split_clause,[],[f334,f330,f272,f337])).
% 0.19/0.51  fof(f272,plain,(
% 0.19/0.51    spl2_32 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.19/0.51  fof(f334,plain,(
% 0.19/0.51    r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_32 | ~spl2_42)),
% 0.19/0.51    inference(backward_demodulation,[],[f274,f332])).
% 0.19/0.51  fof(f274,plain,(
% 0.19/0.51    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_32),
% 0.19/0.51    inference(avatar_component_clause,[],[f272])).
% 0.19/0.51  fof(f333,plain,(
% 0.19/0.51    spl2_42 | ~spl2_2 | ~spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f315,f53,f48,f330])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    spl2_3 <=> l1_pre_topc(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.51  fof(f315,plain,(
% 0.19/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_3)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f55,f50,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f48])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    l1_pre_topc(sK0) | ~spl2_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f53])).
% 0.19/0.51  fof(f275,plain,(
% 0.19/0.51    spl2_32 | ~spl2_4 | ~spl2_5 | ~spl2_27),
% 0.19/0.51    inference(avatar_split_clause,[],[f270,f227,f65,f59,f272])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    spl2_4 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.51  fof(f227,plain,(
% 0.19/0.51    spl2_27 <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.19/0.51  fof(f270,plain,(
% 0.19/0.51    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_5 | ~spl2_27)),
% 0.19/0.51    inference(forward_demodulation,[],[f257,f229])).
% 0.19/0.51  fof(f229,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_27),
% 0.19/0.51    inference(avatar_component_clause,[],[f227])).
% 0.19/0.51  fof(f257,plain,(
% 0.19/0.51    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_5)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f67,f61,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f59])).
% 0.19/0.51  fof(f249,plain,(
% 0.19/0.51    spl2_30 | ~spl2_17 | ~spl2_27),
% 0.19/0.51    inference(avatar_split_clause,[],[f244,f227,f163,f246])).
% 0.19/0.51  fof(f163,plain,(
% 0.19/0.51    spl2_17 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.51  fof(f244,plain,(
% 0.19/0.51    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_17 | ~spl2_27)),
% 0.19/0.51    inference(backward_demodulation,[],[f165,f229])).
% 0.19/0.51  fof(f165,plain,(
% 0.19/0.51    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_17),
% 0.19/0.51    inference(avatar_component_clause,[],[f163])).
% 0.19/0.51  fof(f243,plain,(
% 0.19/0.51    spl2_27 | ~spl2_21 | ~spl2_24),
% 0.19/0.51    inference(avatar_split_clause,[],[f242,f212,f184,f227])).
% 0.19/0.51  fof(f184,plain,(
% 0.19/0.51    spl2_21 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.19/0.51  fof(f212,plain,(
% 0.19/0.51    spl2_24 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.51  fof(f242,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_21 | ~spl2_24)),
% 0.19/0.51    inference(backward_demodulation,[],[f186,f214])).
% 0.19/0.51  fof(f214,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_24),
% 0.19/0.51    inference(avatar_component_clause,[],[f212])).
% 0.19/0.51  fof(f186,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_21),
% 0.19/0.51    inference(avatar_component_clause,[],[f184])).
% 0.19/0.51  fof(f215,plain,(
% 0.19/0.51    spl2_24 | ~spl2_3 | ~spl2_4 | ~spl2_13),
% 0.19/0.51    inference(avatar_split_clause,[],[f210,f118,f59,f53,f212])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    spl2_13 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.19/0.51  fof(f210,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_13)),
% 0.19/0.51    inference(forward_demodulation,[],[f208,f120])).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_13),
% 0.19/0.51    inference(avatar_component_clause,[],[f118])).
% 0.19/0.51  fof(f208,plain,(
% 0.19/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_3 | ~spl2_4)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f55,f61,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.19/0.51  fof(f193,plain,(
% 0.19/0.51    spl2_21 | ~spl2_4 | ~spl2_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f140,f65,f59,f184])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_5)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f67,f61,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(flattening,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 0.19/0.51  fof(f166,plain,(
% 0.19/0.51    spl2_17 | ~spl2_4 | ~spl2_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f149,f65,f59,f163])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_5)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f67,f61,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    spl2_13 | ~spl2_2 | ~spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f109,f53,f48,f118])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_3)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f55,f50,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f63,f53,f48,f65])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f55,f50,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    spl2_4 | ~spl2_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f57,f48,f59])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f50,f41])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f29,f53])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    l1_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 0.19/0.51    inference(negated_conjecture,[],[f10])).
% 0.19/0.51  fof(f10,conjecture,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    spl2_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f30,f48])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ~spl2_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f31,f43])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (15210)------------------------------
% 0.19/0.51  % (15210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15210)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (15210)Memory used [KB]: 11385
% 0.19/0.51  % (15210)Time elapsed: 0.103 s
% 0.19/0.51  % (15210)------------------------------
% 0.19/0.51  % (15210)------------------------------
% 0.19/0.51  % (15201)Success in time 0.171 s
%------------------------------------------------------------------------------
