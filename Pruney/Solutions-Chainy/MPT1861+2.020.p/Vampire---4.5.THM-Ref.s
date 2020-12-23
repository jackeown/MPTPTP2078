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
% DateTime   : Thu Dec  3 13:20:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 300 expanded)
%              Number of leaves         :   32 ( 142 expanded)
%              Depth                    :    7
%              Number of atoms          :  364 ( 917 expanded)
%              Number of equality atoms :   37 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f52,f57,f62,f67,f74,f79,f102,f107,f198,f216,f270,f303,f409,f441,f507,f529,f603,f608,f624,f626])).

fof(f626,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f625,f64,f59,f54,f45,f40,f605])).

fof(f605,plain,
    ( spl3_78
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f40,plain,
    ( spl3_1
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( spl3_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f64,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f625,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f66,f42,f86,f61,f47,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f47,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f86,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f42,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f624,plain,
    ( ~ spl3_77
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f558,f64,f54,f49,f40,f600])).

fof(f600,plain,
    ( spl3_77
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f49,plain,
    ( spl3_3
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f558,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f66,f51,f56,f42,f86,f34])).

fof(f51,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f608,plain,
    ( spl3_78
    | ~ spl3_4
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f597,f526,f54,f605])).

fof(f526,plain,
    ( spl3_72
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f597,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_72 ),
    inference(backward_demodulation,[],[f528,f591])).

fof(f591,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0,sK2)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f528,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f526])).

fof(f603,plain,
    ( spl3_77
    | ~ spl3_4
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f596,f504,f54,f600])).

fof(f504,plain,
    ( spl3_69
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f596,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ spl3_4
    | ~ spl3_69 ),
    inference(backward_demodulation,[],[f506,f591])).

fof(f506,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f504])).

fof(f529,plain,
    ( spl3_72
    | ~ spl3_23
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f524,f406,f195,f526])).

fof(f195,plain,
    ( spl3_23
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f406,plain,
    ( spl3_51
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f524,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1)
    | ~ spl3_23
    | ~ spl3_51 ),
    inference(backward_demodulation,[],[f197,f408])).

fof(f408,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f406])).

fof(f197,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f507,plain,
    ( spl3_69
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f502,f438,f213,f504])).

fof(f213,plain,
    ( spl3_26
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f438,plain,
    ( spl3_56
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f502,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2)
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(backward_demodulation,[],[f215,f440])).

fof(f440,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f438])).

fof(f215,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f441,plain,
    ( spl3_56
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f436,f300,f71,f54,f438])).

fof(f71,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f300,plain,
    ( spl3_36
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f436,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f379,f302])).

fof(f302,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f300])).

fof(f379,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f56,f73,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f73,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f409,plain,
    ( spl3_51
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f404,f267,f76,f59,f406])).

fof(f76,plain,
    ( spl3_8
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f267,plain,
    ( spl3_31
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f404,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f384,f269])).

fof(f269,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f267])).

fof(f384,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f61,f78,f35])).

fof(f78,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f303,plain,
    ( spl3_36
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f298,f99,f71,f59,f54,f300])).

fof(f99,plain,
    ( spl3_11
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f298,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f297,f110])).

fof(f110,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f297,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,sK1) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f237,f101])).

fof(f101,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f237,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f56,f73,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f270,plain,
    ( spl3_31
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f265,f104,f76,f59,f267])).

fof(f104,plain,
    ( spl3_12
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f265,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f242,f106])).

fof(f106,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f242,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f61,f78,f33])).

fof(f216,plain,
    ( spl3_26
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f211,f104,f76,f71,f213])).

fof(f211,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f176,f106])).

fof(f176,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f73,f78,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f198,plain,
    ( spl3_23
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f193,f99,f76,f71,f195])).

fof(f193,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f180,f101])).

fof(f180,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f73,f78,f36])).

fof(f107,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f54,f104])).

fof(f89,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f37])).

fof(f102,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f90,f59,f99])).

fof(f90,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f37])).

fof(f79,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f54,f76])).

fof(f68,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f59,f71])).

fof(f69,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f38])).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

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

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f29,f49,f45])).

fof(f29,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f40])).

fof(f30,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (20806)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (20806)Refutation not found, incomplete strategy% (20806)------------------------------
% 0.21/0.49  % (20806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20788)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (20806)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20806)Memory used [KB]: 10618
% 0.21/0.49  % (20806)Time elapsed: 0.032 s
% 0.21/0.49  % (20806)------------------------------
% 0.21/0.49  % (20806)------------------------------
% 0.21/0.49  % (20791)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (20794)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (20788)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f627,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f43,f52,f57,f62,f67,f74,f79,f102,f107,f198,f216,f270,f303,f409,f441,f507,f529,f603,f608,f624,f626])).
% 0.21/0.49  fof(f626,plain,(
% 0.21/0.49    ~spl3_78 | spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f625,f64,f59,f54,f45,f40,f605])).
% 0.21/0.49  fof(f605,plain,(
% 0.21/0.49    spl3_78 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_1 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_2 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_6 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f625,plain,(
% 0.21/0.49    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f66,f42,f86,f61,f47,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f56,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f624,plain,(
% 0.21/0.49    ~spl3_77 | spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f558,f64,f54,f49,f40,f600])).
% 0.21/0.49  fof(f600,plain,(
% 0.21/0.49    spl3_77 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_3 <=> v2_tex_2(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f558,plain,(
% 0.21/0.49    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f66,f51,f56,f42,f86,f34])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v2_tex_2(sK2,sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f608,plain,(
% 0.21/0.49    spl3_78 | ~spl3_4 | ~spl3_72),
% 0.21/0.49    inference(avatar_split_clause,[],[f597,f526,f54,f605])).
% 0.21/0.49  fof(f526,plain,(
% 0.21/0.49    spl3_72 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.49  fof(f597,plain,(
% 0.21/0.49    r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | (~spl3_4 | ~spl3_72)),
% 0.21/0.49    inference(backward_demodulation,[],[f528,f591])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0,sK2)))) ) | ~spl3_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1) | ~spl3_72),
% 0.21/0.50    inference(avatar_component_clause,[],[f526])).
% 0.21/0.50  fof(f603,plain,(
% 0.21/0.50    spl3_77 | ~spl3_4 | ~spl3_69),
% 0.21/0.50    inference(avatar_split_clause,[],[f596,f504,f54,f600])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    spl3_69 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.21/0.50  fof(f596,plain,(
% 0.21/0.50    r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | (~spl3_4 | ~spl3_69)),
% 0.21/0.50    inference(backward_demodulation,[],[f506,f591])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2) | ~spl3_69),
% 0.21/0.50    inference(avatar_component_clause,[],[f504])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    spl3_72 | ~spl3_23 | ~spl3_51),
% 0.21/0.50    inference(avatar_split_clause,[],[f524,f406,f195,f526])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    spl3_23 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    spl3_51 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.50  fof(f524,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1) | (~spl3_23 | ~spl3_51)),
% 0.21/0.50    inference(backward_demodulation,[],[f197,f408])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl3_51),
% 0.21/0.50    inference(avatar_component_clause,[],[f406])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f195])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    spl3_69 | ~spl3_26 | ~spl3_56),
% 0.21/0.50    inference(avatar_split_clause,[],[f502,f438,f213,f504])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl3_26 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    spl3_56 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.50  fof(f502,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK2) | (~spl3_26 | ~spl3_56)),
% 0.21/0.50    inference(backward_demodulation,[],[f215,f440])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl3_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f438])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2) | ~spl3_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f213])).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    spl3_56 | ~spl3_4 | ~spl3_7 | ~spl3_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f436,f300,f71,f54,f438])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl3_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    spl3_36 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_4 | ~spl3_7 | ~spl3_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f379,f302])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f300])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_4 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f73,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    spl3_51 | ~spl3_5 | ~spl3_8 | ~spl3_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f404,f267,f76,f59,f406])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_8 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl3_31 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_31)),
% 0.21/0.50    inference(forward_demodulation,[],[f384,f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f267])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl3_5 | ~spl3_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f78,f35])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl3_36 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f298,f99,f71,f59,f54,f300])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl3_11 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f297,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    k9_subset_1(u1_struct_0(sK0),sK2,sK1) = k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_7 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f237,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_4 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f73,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    spl3_31 | ~spl3_5 | ~spl3_8 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f265,f104,f76,f59,f267])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_12 <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f242,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl3_5 | ~spl3_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f78,f33])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    spl3_26 | ~spl3_7 | ~spl3_8 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f211,f104,f76,f71,f213])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),sK2) | (~spl3_7 | ~spl3_8 | ~spl3_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f176,f106])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f73,f78,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl3_23 | ~spl3_7 | ~spl3_8 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f193,f99,f76,f71,f195])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),sK1) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f180,f101])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f73,f78,f36])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl3_12 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f89,f54,f104])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f37])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_11 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f90,f59,f99])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f37])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_8 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f54,f76])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_7 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f59,f71])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f38])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_2 | spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f49,f45])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f40])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20788)------------------------------
% 0.21/0.50  % (20788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20788)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20788)Memory used [KB]: 11129
% 0.21/0.50  % (20788)Time elapsed: 0.039 s
% 0.21/0.50  % (20788)------------------------------
% 0.21/0.50  % (20788)------------------------------
% 0.21/0.50  % (20781)Success in time 0.142 s
%------------------------------------------------------------------------------
