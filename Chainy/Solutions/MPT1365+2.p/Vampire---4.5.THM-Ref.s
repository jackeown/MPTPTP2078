%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1365+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 5.58s
% Output     : Refutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 216 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  370 (1064 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10672,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5016,f5021,f5026,f5031,f5036,f5041,f5046,f5051,f6595,f7136,f9039,f10357,f10671])).

fof(f10671,plain,
    ( ~ spl317_3
    | ~ spl317_5
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | spl317_228
    | ~ spl317_708 ),
    inference(avatar_contradiction_clause,[],[f10670])).

fof(f10670,plain,
    ( $false
    | ~ spl317_3
    | ~ spl317_5
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | spl317_228
    | ~ spl317_708 ),
    inference(subsumption_resolution,[],[f10669,f6589])).

fof(f6589,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl317_5 ),
    inference(backward_demodulation,[],[f6223,f6222])).

fof(f6222,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl317_5 ),
    inference(unit_resulting_resolution,[],[f5035,f3505])).

fof(f3505,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2483])).

fof(f2483,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f5035,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl317_5 ),
    inference(avatar_component_clause,[],[f5033])).

fof(f5033,plain,
    ( spl317_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_5])])).

fof(f6223,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl317_5 ),
    inference(unit_resulting_resolution,[],[f5035,f3506])).

fof(f3506,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2484])).

fof(f2484,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f10669,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl317_3
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | spl317_228
    | ~ spl317_708 ),
    inference(unit_resulting_resolution,[],[f5050,f5045,f5025,f5040,f3882,f6594,f10196,f3519])).

fof(f3519,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f2501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2500])).

fof(f2500,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2460])).

fof(f2460,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(f10196,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl317_708 ),
    inference(avatar_component_clause,[],[f10195])).

fof(f10195,plain,
    ( spl317_708
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_708])])).

fof(f6594,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | spl317_228 ),
    inference(avatar_component_clause,[],[f6592])).

fof(f6592,plain,
    ( spl317_228
  <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_228])])).

fof(f3882,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f5040,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl317_6 ),
    inference(avatar_component_clause,[],[f5038])).

fof(f5038,plain,
    ( spl317_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_6])])).

fof(f5025,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl317_3 ),
    inference(avatar_component_clause,[],[f5023])).

fof(f5023,plain,
    ( spl317_3
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_3])])).

fof(f5045,plain,
    ( l1_pre_topc(sK0)
    | ~ spl317_7 ),
    inference(avatar_component_clause,[],[f5043])).

fof(f5043,plain,
    ( spl317_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_7])])).

fof(f5050,plain,
    ( v2_pre_topc(sK0)
    | ~ spl317_8 ),
    inference(avatar_component_clause,[],[f5048])).

fof(f5048,plain,
    ( spl317_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_8])])).

fof(f10357,plain,
    ( spl317_708
    | ~ spl317_5
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | ~ spl317_304
    | ~ spl317_550 ),
    inference(avatar_split_clause,[],[f10313,f8914,f7036,f5048,f5043,f5038,f5033,f10195])).

fof(f7036,plain,
    ( spl317_304
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_304])])).

fof(f8914,plain,
    ( spl317_550
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_550])])).

fof(f10313,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl317_5
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | ~ spl317_304
    | ~ spl317_550 ),
    inference(forward_demodulation,[],[f10276,f3881])).

fof(f3881,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f10276,plain,
    ( v4_pre_topc(k3_xboole_0(sK2,sK1),sK0)
    | ~ spl317_5
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8
    | ~ spl317_304
    | ~ spl317_550 ),
    inference(unit_resulting_resolution,[],[f5050,f5045,f7038,f5035,f5040,f8916,f3980])).

fof(f3980,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2686])).

fof(f2686,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2685])).

fof(f2685,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2114])).

fof(f2114,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f8916,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl317_550 ),
    inference(avatar_component_clause,[],[f8914])).

fof(f7038,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl317_304 ),
    inference(avatar_component_clause,[],[f7036])).

fof(f9039,plain,
    ( spl317_550
    | ~ spl317_3
    | ~ spl317_4
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8 ),
    inference(avatar_split_clause,[],[f9038,f5048,f5043,f5038,f5028,f5023,f8914])).

fof(f5028,plain,
    ( spl317_4
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_4])])).

fof(f9038,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl317_3
    | ~ spl317_4
    | ~ spl317_6
    | ~ spl317_7
    | ~ spl317_8 ),
    inference(subsumption_resolution,[],[f9037,f5050])).

fof(f9037,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_3
    | ~ spl317_4
    | ~ spl317_6
    | ~ spl317_7 ),
    inference(subsumption_resolution,[],[f9036,f5045])).

fof(f9036,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_3
    | ~ spl317_4
    | ~ spl317_6 ),
    inference(subsumption_resolution,[],[f9035,f5030])).

fof(f5030,plain,
    ( v8_pre_topc(sK0)
    | ~ spl317_4 ),
    inference(avatar_component_clause,[],[f5028])).

fof(f9035,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_3
    | ~ spl317_6 ),
    inference(subsumption_resolution,[],[f8060,f5025])).

fof(f8060,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_6 ),
    inference(resolution,[],[f5040,f3526])).

fof(f3526,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2509])).

fof(f2509,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2508])).

fof(f2508,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2458])).

fof(f2458,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f7136,plain,
    ( spl317_304
    | ~ spl317_2
    | ~ spl317_4
    | ~ spl317_5
    | ~ spl317_7
    | ~ spl317_8 ),
    inference(avatar_split_clause,[],[f7135,f5048,f5043,f5033,f5028,f5018,f7036])).

fof(f5018,plain,
    ( spl317_2
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_2])])).

fof(f7135,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl317_2
    | ~ spl317_4
    | ~ spl317_5
    | ~ spl317_7
    | ~ spl317_8 ),
    inference(subsumption_resolution,[],[f7134,f5050])).

fof(f7134,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_2
    | ~ spl317_4
    | ~ spl317_5
    | ~ spl317_7 ),
    inference(subsumption_resolution,[],[f7133,f5045])).

fof(f7133,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_2
    | ~ spl317_4
    | ~ spl317_5 ),
    inference(subsumption_resolution,[],[f7132,f5030])).

fof(f7132,plain,
    ( ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_2
    | ~ spl317_5 ),
    inference(subsumption_resolution,[],[f6296,f5020])).

fof(f5020,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl317_2 ),
    inference(avatar_component_clause,[],[f5018])).

fof(f6296,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl317_5 ),
    inference(resolution,[],[f5035,f3526])).

fof(f6595,plain,
    ( ~ spl317_228
    | spl317_1
    | ~ spl317_5 ),
    inference(avatar_split_clause,[],[f6590,f5033,f5013,f6592])).

fof(f5013,plain,
    ( spl317_1
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl317_1])])).

fof(f6590,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | spl317_1
    | ~ spl317_5 ),
    inference(backward_demodulation,[],[f5015,f6222])).

fof(f5015,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl317_1 ),
    inference(avatar_component_clause,[],[f5013])).

fof(f5051,plain,(
    spl317_8 ),
    inference(avatar_split_clause,[],[f3464,f5048])).

fof(f3464,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3066])).

fof(f3066,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2477,f3065,f3064,f3063])).

fof(f3063,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3064,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3065,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2477,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2476])).

fof(f2476,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2464])).

fof(f2464,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2463])).

fof(f2463,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

fof(f5046,plain,(
    spl317_7 ),
    inference(avatar_split_clause,[],[f3465,f5043])).

fof(f3465,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5041,plain,(
    spl317_6 ),
    inference(avatar_split_clause,[],[f3466,f5038])).

fof(f3466,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5036,plain,(
    spl317_5 ),
    inference(avatar_split_clause,[],[f3467,f5033])).

fof(f3467,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5031,plain,(
    spl317_4 ),
    inference(avatar_split_clause,[],[f3468,f5028])).

fof(f3468,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5026,plain,(
    spl317_3 ),
    inference(avatar_split_clause,[],[f3469,f5023])).

fof(f3469,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5021,plain,(
    spl317_2 ),
    inference(avatar_split_clause,[],[f3470,f5018])).

fof(f3470,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f3066])).

fof(f5016,plain,(
    ~ spl317_1 ),
    inference(avatar_split_clause,[],[f3471,f5013])).

fof(f3471,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f3066])).
%------------------------------------------------------------------------------
